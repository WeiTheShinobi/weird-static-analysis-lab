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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        Deque<JMethod> queue = new LinkedList<>();

        queue.add(entry);
        callGraph.addEntryMethod(entry);
        while (!queue.isEmpty()) {
            var method = queue.pollFirst();
            if (callGraph.contains(method)) {
                continue;
            }
            callGraph.addReachableMethod(method);
            var invokeStream = callGraph.callSitesIn(method);
            invokeStream.forEach(cs -> {
                for (JMethod targetMethod : resolve(cs)) {
                    if (targetMethod != null) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, targetMethod));
                        queue.addLast(targetMethod);
                    }
                }
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        var result = new HashSet<JMethod>();
        var methodRef = callSite.getMethodRef();
        var declareClass = methodRef.getDeclaringClass();
        var kind = CallGraphs.getCallKind(callSite);

        switch (kind) {
            case STATIC -> result.add(declareClass.getDeclaredMethod(methodRef.getSubsignature()));
            case SPECIAL -> result.add(dispatch(declareClass, methodRef.getSubsignature()));
            case VIRTUAL, INTERFACE -> {
                ArrayDeque<JClass> subclasses = new ArrayDeque<>();
                HashSet<JClass> set = new HashSet<>();
                subclasses.addLast(declareClass);
                set.add(declareClass);
                while (!subclasses.isEmpty()) {
                    JClass subclass = subclasses.pollFirst();
                    result.add(dispatch(subclass, methodRef.getSubsignature()));
                    for (JClass jClass : (hierarchy.getDirectSubclassesOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                    for (JClass jClass : (hierarchy.getDirectSubinterfacesOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                    for (JClass jClass : (hierarchy.getDirectImplementorsOf(subclass))) {
                        if (!set.contains(jClass)) {
                            set.add(jClass);
                            subclasses.addLast(jClass);
                        }
                    }
                }
            }
        }

        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }
        if (jclass.getDeclaredMethod(subsignature) != null && !jclass.getDeclaredMethod(subsignature).isAbstract()) {
            return jclass.getDeclaredMethod(subsignature);
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
