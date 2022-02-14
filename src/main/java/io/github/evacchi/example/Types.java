package io.github.evacchi.example;


import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.stream.Collectors.joining;

sealed interface Term {
    record Lambda(String v, Term body) implements Term { public String toString() { return String.format("(λ%s.%s)", v, body); } }
    static Lambda Lambda(String v, Term body) { return new Lambda(v, body);}

    record Var(String name) implements Term { public String toString() { return name; } }
    static Var Var(String name) { return new Var(name); }

    record Apply(Term fn, Term arg) implements Term { public String toString() { return String.format("(%s %s)", fn, arg); } }
    static Apply Apply(Term fn, Term arg) { return new Apply(fn, arg); }

    record Let(String v, Term defn, Term body) implements Term { public String toString() { return String.format("let %s = %s in %s", v, defn, body); } }
    static Let Let(String v, Term defn, Term body) { return new Let(v, defn, body); }

    record LetRec(String v, Term defn, Term body) implements Term { public String toString() { return String.format("letrec %s = %s in %s", v, defn, body); } }
    static LetRec LetRec(String v, Term defn, Term body) { return new LetRec(v, defn, body); }
}

sealed interface Type {
    final class TypeVariable implements Type {
        private static char next = 'a';
        String v; TypeVariable(String v) { this.v =v ; }
        public String toString() { return v; }
        public boolean equals(Object o) { return o instanceof TypeVariable tv && Objects.equals(v, tv.v); }
        public int hashCode() { return Objects.hash(v); }
    }
    static TypeVariable TypeVariable(String v) {return new TypeVariable(v);}
    static TypeVariable TypeVariable() { return new TypeVariable(String.valueOf(TypeVariable.next++)); }

    record Arrow(Type t1, Type t2) implements Type { public String toString() { return String.format("(%s->%s)", t1, t2); }}
    static Arrow Arrow(Type t1, Type t2) {return new Arrow(t1,t2);}

    record TypeCons(String name, List<Type> types) implements Type {
        public String toString() {
            return name + (types.isEmpty() ? "" : types.stream().map(Objects::toString).collect(joining(",", "<", ">"))); }}
    static TypeCons TypeCons(String name, List<Type> types) { return new TypeCons(name, types); }

    abstract class Subst {
        static Subst Empty = new Subst() { Type lookup(TypeVariable tv) { return tv; } };
        abstract Type lookup(TypeVariable tv);
        Type apply(Type t) {
            return switch(t) {
                case TypeVariable tv -> {
                    var u = lookup(tv);
                    yield (t.equals(u)) ? t : apply(u);
                }
                case Arrow a -> Arrow(apply(a.t1()), apply(a.t2()));
                case TypeCons tc -> TypeCons(tc.name(), tc.types().stream().map(this::apply).toList());
            };
        }
        Env apply(Env env) {

        }
        Subst extend(TypeVariable x, Type t) {
            return new Subst() {
                @Override
                Type lookup(TypeVariable y) {
                    return (x.equals(y))? t : lookup(y);
                }
            };
        }
    }

    record TypeScheme(List<TypeVariable> typeVars, Type t) {
        public Type newInstance() {
            var subst = Subst.Empty;
            for (TypeVariable tv : typeVars) {
                subst = subst.extend(tv, TypeVariable());
            }
            return subst.apply(t);
        }
    }
    static TypeScheme TypeScheme(List<TypeVariable> typeVars, Type t) { return new TypeScheme(typeVars, t); }

    final class Env {
        private Map<String, TypeScheme> env;
        TypeScheme lookup(String name) { return env.get(name); }
        TypeScheme gen(Type t) {
            TypeScheme()
        }
    }

    static List<TypeVariable> tyVars(Type t) {
        return switch (t) {
            case TypeVariable tv -> List.of(tv);
            case Arrow a -> Stream.concat(tyVars(a.t1()).stream(), tyVars(a.t2()).stream()).toList();
            case TypeCons tc -> tc.types().stream().flatMap(tp -> tyVars(tp).stream()).collect(Collectors.toList());
        };
    }
}

