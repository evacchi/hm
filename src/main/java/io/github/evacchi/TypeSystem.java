package io.github.evacchi;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import static io.github.evacchi.Term.*;
import static io.github.evacchi.Type.*;
import static java.util.stream.Collectors.*;

sealed interface Type {

    final class TypeVariable implements Type {
        static char nextVariableName = 'a';

        Type instance = UNKNOWN;
        String name = "";

        @Override
        public String toString() {
            if (name.isEmpty()) {
                name = String.valueOf(nextVariableName++); //A device that does not wastefully consume the alphabet when displaying variable names
            }
            return name;
        }

    }
    static TypeVariable TypeVariable() { return new TypeVariable(); }

    sealed class TypeOperator implements Type {
        final String name; final List<Type> types;
        public TypeOperator(String name, List<Type> types) {
            this.name = name; this.types = types;
        }
        public String name() { return name; }
        public List<Type> types() { return types; }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            TypeOperator that = (TypeOperator) o;
            return Objects.equals(name, that.name) && Objects.equals(types, that.types);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name, types);
        }

        @Override
        public String toString() {
            return name + (types.isEmpty() ? "" : types.stream().map(Objects::toString).collect(joining(",", "<", ">")));
        }
    }
    final class Function extends TypeOperator {
        public Function(Type fromType, Type toType) {
            super("->", List.of(fromType, toType));
        }

        @Override
        public String toString() {
            return types.get(0) + " -> " + types.get(1);
        }
    }

    static TypeOperator TypeOperator(String name, List<Type> types) { return new TypeOperator(name, types); }
    static TypeOperator Function(Type fromType, Type toType) { return new Function(fromType, toType); }

    TypeOperator INTEGER = TypeOperator("int", List.of());
    TypeOperator BOOLEAN = TypeOperator("bool", List.of());
    TypeOperator UNKNOWN = TypeOperator("unknown", List.of());

}



public interface TypeSystem {
    static Map<String,Type> newEnv(Map<String, Type> env, String name, Type t) {
        var env2 = new HashMap<>(env);
        env2.put(name, t);
        return env2;
    }

    static Set<Type> newSet(Set<Type> s, Type t) {
        var ss = new HashSet<>(s);
        ss.add(t);
        return ss;
    }

    static Type analyse(Term node, Map<String, Type> env, Set<Type> nonGeneric) {
        return switch (node) {
            case Id id -> getType(id.name(), env, nonGeneric);
            case Apply app -> {
                var funType = analyse(app.fn(), env, nonGeneric);
                var argType = analyse(app.arg(), env, nonGeneric);
                var resultType = TypeVariable();
                unify(Function(argType, resultType), funType);
                yield resultType;
            }
            case Lambda l -> {
                var argType = TypeVariable();
                var resultType = analyse(l.body(), newEnv(env, l.v(), argType), newSet(nonGeneric, argType));
                yield Function(argType, resultType);
            }
            case Let l -> {
                var defnType = analyse(l.defn(), env, nonGeneric);
                yield analyse(l.body(), newEnv(env, l.v(), defnType), nonGeneric);
            }
            case LetRec l -> {
                var newType = TypeVariable();
                var newEnv = newEnv(env, l.v(), newType);
                var defnType = analyse(l.defn(), newEnv, newSet(nonGeneric, newType));
                unify(newType, defnType);
                yield analyse(l.body(), newEnv, nonGeneric);
            }
        };
    }

    static void unify(Type t1, Type t2) {
        var a = prune(t1);
        var b = prune(t2);
        if (a instanceof TypeVariable tv) {
            if (!a.equals(b)) {
                if (occursInType(a, b))
                    throw new RuntimeException("recursive unification");
                else
                    tv.instance = b;
            }
        } else if (a instanceof TypeOperator && b instanceof TypeVariable) {
            unify(b, a);
        } else if (a instanceof TypeOperator aa && b instanceof TypeOperator bb) {
            if (!aa.name().equals(bb.name()) || aa.types().size() != bb.types().size()) {
                throw new RuntimeException("Type mismatch ${a} != ${b}");
            }
            for (int i = 0; i < aa.types().size(); i++) {
                unify(aa.types().get(i), bb.types().get(i));
            }
        }
    }

    static Type prune(Type t) {
        if (t instanceof TypeVariable tv && tv.instance != UNKNOWN){
            tv.instance = prune(tv.instance);
            return tv.instance;
        } else return t;
    }

    static Type getType(String name, Map<String, Type> env, Set<Type> nonGeneric) {
        Type type = env.get(name);
        if (type == null) {
            if (isIntegerTLiteral(name)) return INTEGER;
        } else{
            return fresh(type, nonGeneric);
        }
        if (isIntegerTLiteral(name)) {
            return INTEGER;
        }
        throw new RuntimeException("Undefined symbol ${name}");

    }

    static boolean isIntegerTLiteral(String name) {
        try {
            Long.parseLong(name);
            return true;
        } catch (NumberFormatException e) {
            return false;
        }
    }


    static Type fresh(Type t, Set<Type> nonGeneric) {
        var mappings = new HashMap<Type, Type>();
        return freshrec(t, mappings, nonGeneric);
    }
    static Type freshrec(Type tp, Map<Type, Type> mappings, Set<Type> nonGeneric) {
        var p = prune(tp);
        return switch(p) {
            case TypeVariable tv -> {
                if (isGeneric(p, nonGeneric))
                    yield mappings.computeIfAbsent(p, (k) -> TypeVariable());
                else yield p;
            }
            case TypeOperator to -> TypeOperator(to.name(), to.types().stream().map(it -> freshrec(it, mappings, nonGeneric)).toList());
        };
    }




    static boolean isGeneric( Type v,   Set<Type> nonGeneric) {
        return !occursIn(v, nonGeneric);
    }

    static boolean occursIn(Type t, Collection<Type> types) {
        return types.stream().anyMatch(it -> occursInType(t, it));
    }

    static boolean occursInType( Type v, Type type2) {
        var prunedType2 = prune(type2);
        if (prunedType2 == v) return true;
        else if (prunedType2 instanceof TypeOperator to) return occursIn(v, to.types());
        else return false;
    }

}
