/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.graph.AbstractEdge;
import soot.toolkits.scalar.LiveLocals;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Deque<Stmt> queue = new LinkedList<>();
        Set<Stmt> reachableStmt = new HashSet<>();
        Set<Stmt> seen = new HashSet<>();

        queue.add(cfg.getEntry());
        seen.add(cfg.getEntry());
        while (!queue.isEmpty()) {
            var stmt = queue.pollFirst();
            seen.add(stmt);
            if (stmt instanceof AssignStmt<?, ?> assignStmt) {
                var lValue = assignStmt.getLValue();
                reachableStmt.add(stmt);
                if (lValue instanceof Var def) {
                    var noSideEffect = hasNoSideEffect(assignStmt.getRValue());
                    var noUse = !liveVars.getResult(stmt).contains(def);
                    if (noSideEffect && noUse) {
                        reachableStmt.remove(stmt);
                    }
                }
                for (var succ : cfg.getSuccsOf(stmt)) {
                    if (!seen.contains(succ)) {
                        queue.add(succ);
                    }
                }
            } else if (stmt instanceof If ifStmt) {
                reachableStmt.add(stmt);
                var stmtLiveVar = constants.getResult(stmt);
                var cond = ifStmt.getCondition();
                var eval = handleConditionExp(cond, stmtLiveVar);
                if (eval.isConstant()) {
                    if (eval.getConstant() == 1) {
                        for (var edge : cfg.getOutEdgesOf(stmt)) {
                            if (edge.getKind() == Edge.Kind.IF_TRUE) {
                                queue.add(edge.getTarget());
                            }
                        }
                    } else {
                        for (var edge : cfg.getOutEdgesOf(stmt)) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                queue.add(edge.getTarget());
                            }
                        }
                    }
                } else {
                    for (var succ : cfg.getSuccsOf(stmt)) {
                        if (!seen.contains(succ)) {
                            queue.add(succ);
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt switchStmt) {
                var stmtLiveVar = constants.getResult(stmt);
                var value = stmtLiveVar.get(switchStmt.getVar());
                reachableStmt.add(stmt);
                if (value.isConstant()) {
                    int constant = value.getConstant();
                    boolean match = false;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                            int caseValue = edge.getCaseValue();
                            if (caseValue == constant) {
                                match = true;
                                if (!seen.contains(edge.getTarget()))
                                    queue.addLast(edge.getTarget());
                            }
                        }
                    }
                    if (!match) {
                        Stmt defaultTarget = switchStmt.getDefaultTarget();  // 获取default对应的目标语句
                        if (!seen.contains(defaultTarget))
                            queue.addLast(defaultTarget);
                    }
                } else {
                    for (Stmt succ : cfg.getSuccsOf(switchStmt)) {
                        if (!seen.contains(succ))
                            queue.addLast(succ);
                    }
                }
            } else {
                reachableStmt.add(stmt);
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!seen.contains(succ))
                        queue.addLast(succ);
                }
            }
        }

        for (Stmt stmt : ir.getStmts()) {
            if (!reachableStmt.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }


    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    private static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof ConditionExp conditionExp) {
            return handleConditionExp(conditionExp, in);
        }
        return Value.getNAC();
    }

    private static Value handleConditionExp(ConditionExp conditionExp, CPFact in) {
        var a = evaluate(conditionExp.getOperand1(), in);
        var b = evaluate(conditionExp.getOperand2(), in);
        if (a.isUndef() || b.isUndef()) {
            return Value.getUndef();
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.EQ)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() == b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.NE)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() != b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.LT)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() < b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.GT)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() > b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.LE)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() <= b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        if (conditionExp.getOperator().equals(ConditionExp.Op.GE)) {
            if (a.isConstant() && b.isConstant()) {
                return a.getConstant() >= b.getConstant() ? Value.makeConstant(1) : Value.makeConstant(0);
            }
        }
        return Value.getNAC();
    }
}
