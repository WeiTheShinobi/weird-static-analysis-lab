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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.contains(method)) {
            return;
        }
        callGraph.addReachableMethod(method);
        for (var stmt : method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            var pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(pointer, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var lPointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var rPointer = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(rPointer, lPointer);
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                var lValue = pointerFlowGraph.getVarPtr(stmt.getLValue());
                var field = stmt.getFieldRef().resolve();
                var rValue = pointerFlowGraph.getStaticField(field);
                addPFGEdge(rValue, lValue);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                var rValue = pointerFlowGraph.getVarPtr(stmt.getRValue());
                var field = stmt.getFieldRef().resolve();
                var lValue = pointerFlowGraph.getStaticField(field);
                addPFGEdge(rValue, lValue);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var method = resolveCallee(null, stmt);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))) {
                addReachable(method);
                InvokeExp invokeExp = stmt.getInvokeExp();
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    Var actual = invokeExp.getArg(i);
                    VarPtr actualPtr = pointerFlowGraph.getVarPtr(actual);
                    Var form = method.getIR().getParam(i);
                    VarPtr formPtr = pointerFlowGraph.getVarPtr(form);
                    addPFGEdge(actualPtr, formPtr);
                }
                if (stmt.getLValue() != null) {
                    for (Var returnVar : method.getIR().getReturnVars()) {
                        VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                        VarPtr lVarPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        addPFGEdge(returnVarPtr, lVarPtr);
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var diff = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr varPtr) {
                var var = varPtr.getVar();
                for (var obj : diff) {
                    for (var storeField : var.getStoreFields()) {
                        var rValue = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        var field = storeField.getFieldRef().resolve();
                        var lValue = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(rValue, lValue);
                    }
                    for (var loadField : var.getLoadFields()) {
                        var lValue = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        var field = loadField.getFieldRef().resolve();
                        var rValue = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(rValue, lValue);
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        var rValue = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(rValue, arrayIndex);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        var lValue = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, lValue);
                    }
                    processCall(var, obj);
                }
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var diff = new PointsToSet();
        for (var obj : pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                diff.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        }
        if (!diff.isEmpty()) {
            for (var succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, pointsToSet);
            }
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var invoke : var.getInvokes()) {
            var method = resolveCallee(recv, invoke);
            var thisPointer = pointerFlowGraph.getVarPtr(method.getIR().getThis());
            workList.addEntry(thisPointer, new PointsToSet(recv));

            var edge = getInvokeJMethodEdge(invoke, method);
            if (callGraph.addEdge(edge)) {
                addReachable(method);
                var args = invoke.getRValue().getArgs();
                var params = method.getIR().getParams();
                for (var i = 0; i < method.getParamCount(); i++) {
                    var arg = pointerFlowGraph.getVarPtr(args.get(i));
                    var param = pointerFlowGraph.getVarPtr(params.get(i));
                    addPFGEdge(arg, param);
                }

                var returnVar = invoke.getLValue();
                if (returnVar != null) {
                    for (var v : method.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(v), pointerFlowGraph.getVarPtr(returnVar));
                    }
                }
            }
        }
    }

    private static Edge<Invoke, JMethod> getInvokeJMethodEdge(Invoke invoke, JMethod method) {
        var edge = new Edge<>(CallKind.OTHER, invoke, method);
        if (invoke.isInterface()) {
            edge = new Edge<>(CallKind.INTERFACE, invoke, method);
        }
        if (invoke.isDynamic()) {
            edge = new Edge<>(CallKind.DYNAMIC, invoke, method);
        }
        if (invoke.isSpecial()) {
            edge = new Edge<>(CallKind.SPECIAL, invoke, method);
        }
        if (invoke.isVirtual()) {
            edge = new Edge<>(CallKind.VIRTUAL, invoke, method);
        }
        return edge;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
