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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var fact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(target.get(var), fact.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.isConstant() && v2.isConstant()) {
            return (v1.getConstant() == v2.getConstant()) ? v1 : Value.getNAC();
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact inCopy = in.copy();
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            if (defStmt.getDef().isPresent()) {
                var lValue = defStmt.getDef().get();
                if ((lValue instanceof Var) && canHoldInt((Var) lValue)) {
                    inCopy.update((Var) lValue, evaluate(defStmt.getRValue(), inCopy));
                }
            }
        }
        return out.copyFrom(inCopy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof ArithmeticExp arithmeticExp) {
            return handleArithmeticExp(arithmeticExp, in);
        }
        if (exp instanceof ConditionExp conditionExp) {
            return handleConditionExp(conditionExp, in);
        }
        if (exp instanceof ShiftExp shiftExp) {
            return handleShiftExp(shiftExp, in);
        }
        if (exp instanceof BitwiseExp bitwiseExp) {
            return handleBitwiseExp(bitwiseExp, in);
        }
        return Value.getNAC();
    }

    private static Value handleShiftExp(ShiftExp shiftExp, CPFact in) {
        var a = evaluate(shiftExp.getOperand1(), in);
        var b = evaluate(shiftExp.getOperand2(), in);
        if (a.isUndef() || b.isUndef()) {
            return Value.getUndef();
        }
        if (shiftExp.getOperator().equals(ShiftExp.Op.SHL)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() << b.getConstant());
            }
        }
        if (shiftExp.getOperator().equals(ShiftExp.Op.SHR)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() >> b.getConstant());
            }
        }
        if (shiftExp.getOperator().equals(ShiftExp.Op.USHR)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() >>> b.getConstant());
            }
        }
        return Value.getNAC();
    }

    private static Value handleBitwiseExp(BitwiseExp bitwiseExp, CPFact in) {
        var a = evaluate(bitwiseExp.getOperand1(), in);
        var b = evaluate(bitwiseExp.getOperand2(), in);
        if (a.isUndef() || b.isUndef()) {
            return Value.getUndef();
        }
        if (bitwiseExp.getOperator().equals(BitwiseExp.Op.OR)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() | b.getConstant());
            }
        }
        if (bitwiseExp.getOperator().equals(BitwiseExp.Op.AND)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() & b.getConstant());
            }
        }
        if (bitwiseExp.getOperator().equals(BitwiseExp.Op.XOR)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() ^ b.getConstant());
            }
        }
        return Value.getNAC();
    }

    private static Value handleArithmeticExp(ArithmeticExp arithmeticExp, CPFact in) {
        var a = evaluate(arithmeticExp.getOperand1(), in);
        var b = evaluate(arithmeticExp.getOperand2(), in);
        if (a.isUndef() || b.isUndef()) {
            return Value.getUndef();
        }
        if (arithmeticExp.getOperator().equals(ArithmeticExp.Op.ADD)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() + b.getConstant());
            }
        }
        if (arithmeticExp.getOperator().equals(ArithmeticExp.Op.SUB)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() - b.getConstant());
            }
        }
        if (arithmeticExp.getOperator().equals(ArithmeticExp.Op.MUL)) {
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() * b.getConstant());
            }
        }
        if (arithmeticExp.getOperator().equals(ArithmeticExp.Op.DIV)) {
            if (b.isConstant() && b.getConstant() == 0) {
                return Value.getUndef();
            }
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() / b.getConstant());
            }
        }
        if (arithmeticExp.getOperator().equals(ArithmeticExp.Op.REM)) {
            if (b.isConstant() && b.getConstant() == 0) {
                return Value.getUndef();
            }
            if (a.isConstant() && b.isConstant()) {
                return Value.makeConstant(a.getConstant() % b.getConstant());
            }
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
