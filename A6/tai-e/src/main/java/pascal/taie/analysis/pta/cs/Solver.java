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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            for (var stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(new StmtProcessor(csMethod));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            var csVar = csManager.getCSVar(context, stmt.getLValue());
            var obj = heapModel.getObj(stmt);
            var objCx = contextSelector.selectHeapContext(csMethod, obj);
            var csObj = csManager.getCSObj(objCx, obj);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var l = csManager.getCSVar(context, stmt.getLValue());
            var r = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(r, l);
            return null;
        }

        public Void visit(StoreField stmt) {
            var field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                var from = csManager.getCSVar(context, stmt.getRValue());
                var to = csManager.getStaticField(field);
                addPFGEdge(from, to);
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            var field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                var to = csManager.getCSVar(context, stmt.getLValue());
                var from = csManager.getStaticField(field);
                addPFGEdge(from, to);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                var m = resolveCallee(null, stmt);
                var csCallSite = csManager.getCSCallSite(context, stmt);
                var ctx = contextSelector.selectContext(csCallSite, m); // c_t
                var targetMethod = csManager.getCSMethod(ctx, m);
                var edge = new Edge<>(CallKind.STATIC, csCallSite, targetMethod);
                if (callGraph.addEdge(edge)) {
                    addReachable(targetMethod);
                    for (int i = 0; i < m.getParamCount(); i++) {
                        var arg = csManager.getCSVar(context, stmt.getRValue().getArg(i));
                        var param = csManager.getCSVar(ctx, m.getIR().getParam(i));
                        addPFGEdge(arg, param);
                    }
                    var lVar = stmt.getLValue();
                    if (lVar != null) {
                        var lv = csManager.getCSVar(context, lVar);
                        for (Var ret: m.getIR().getReturnVars()) {
                            var csRet = csManager.getCSVar(ctx, ret);
                            addPFGEdge(csRet, lv);
                        }
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
            if (entry.pointer() instanceof CSVar entryVar) {
                for (var obj : diff) {
                    var var = entryVar.getVar();
                    for (var storeField : var.getStoreFields()) {
                        var rValue = csManager.getCSVar(entryVar.getContext(), storeField.getRValue());
                        var lValue = csManager.getInstanceField(obj, storeField.getLValue().getFieldRef().resolve());
                        addPFGEdge(rValue, lValue);
                    }
                    for (var loadField : var.getLoadFields()) {
                        var lValue = csManager.getCSVar(entryVar.getContext(), loadField.getLValue());
                        var rValue = csManager.getInstanceField(obj, loadField.getRValue().getFieldRef().resolve());
                        addPFGEdge(rValue, lValue);
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        var rValue = csManager.getCSVar(entryVar.getContext(), storeArray.getRValue());
                        var arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(rValue, arrayIndex);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        var lValue = csManager.getCSVar(entryVar.getContext(), loadArray.getLValue());
                        var arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, lValue);
                    }
                    processCall(entryVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var diff = PointsToSetFactory.make();
        for (var obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                diff.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        }
        if (diff.isEmpty()) {
            return diff;
        }
        for (var s : pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(s, pointsToSet);
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (var invoke : recv.getVar().getInvokes()) {
            var method = resolveCallee(recvObj, invoke);
            var csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            var cx = contextSelector.selectContext(csCallSite, recvObj, method);
            var thisVar = method.getIR().getThis();
            var thisPointer = csManager.getCSVar(cx, thisVar);

            workList.addEntry(thisPointer, PointsToSetFactory.make(recvObj));

            var csMethod = csManager.getCSMethod(cx, method);
            var edge = getInvokeJMethodEdge(csCallSite, csMethod);
            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);
                for (int i = 0; i < csMethod.getMethod().getParamCount(); i++) {
                    var param = csMethod.getMethod().getIR().getParam(i);
                    var argument = csCallSite.getCallSite().getInvokeExp().getArg(i);

                    addPFGEdge(csManager.getCSVar(recv.getContext(), argument), csManager.getCSVar(cx, param));
                }

                var callSiteReturnVal = csCallSite.getCallSite().getLValue();
                if (callSiteReturnVal != null) {
                    for (var r : csMethod.getMethod().getIR().getReturnVars()) {
                        var methodReturnVal = csManager.getCSVar(cx, r);
                        addPFGEdge(methodReturnVal, csManager.getCSVar(recv.getContext(), callSiteReturnVal));
                    }
                }
            }
        }
    }

    private static Edge<CSCallSite, CSMethod> getInvokeJMethodEdge(CSCallSite invoke, CSMethod method) {
        var edge = new Edge<>(CallKind.OTHER, invoke, method);
        if (invoke.getCallSite().isInterface()) {
            edge = new Edge<>(CallKind.INTERFACE, invoke, method);
        }
        if (invoke.getCallSite().isDynamic()) {
            edge = new Edge<>(CallKind.DYNAMIC, invoke, method);
        }
        if (invoke.getCallSite().isSpecial()) {
            edge = new Edge<>(CallKind.SPECIAL, invoke, method);
        }
        if (invoke.getCallSite().isVirtual()) {
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
