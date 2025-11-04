/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> vals;
    for (auto &ex : rands) {
        vals.push_back(ex->eval(e));
    }
    return evalRator(vals);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
    if (it != primitive_map.end()) {
                // Bind the primitive parameters in a temporary environment and evaluate
                Assoc tmp = empty();
                for (size_t i = 0; i < it->second.second.size(); ++i) {
                    // For primitives with parameters, leave them unbound here; Apply/Lambda will supply during call
                    // Here we just return the procedure closure with environment tmp
                }
                return ProcedureV(it->second.second, it->second.first, e);
    }
      }
    }
    return matched_value;
}

Value Plus::evalRator(const Value &a, const Value &b) {
    if (a->v_type == V_INT && b->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return IntegerV(n1 + n2);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_INT) {
        auto r = dynamic_cast<Rational*>(a.get());
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return RationalV(r->numerator + n2 * r->denominator, r->denominator);
    }
    if (a->v_type == V_INT && b->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        auto r = dynamic_cast<Rational*>(b.get());
        return RationalV(n1 * r->denominator + r->numerator, r->denominator);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_RATIONAL) {
        auto r1 = dynamic_cast<Rational*>(a.get());
        auto r2 = dynamic_cast<Rational*>(b.get());
        return RationalV(r1->numerator * r2->denominator + r2->numerator * r1->denominator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &a, const Value &b) {
    if (a->v_type == V_INT && b->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return IntegerV(n1 - n2);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_INT) {
        auto r = dynamic_cast<Rational*>(a.get());
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return RationalV(r->numerator - n2 * r->denominator, r->denominator);
    }
    if (a->v_type == V_INT && b->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        auto r = dynamic_cast<Rational*>(b.get());
        return RationalV(n1 * r->denominator - r->numerator, r->denominator);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_RATIONAL) {
        auto r1 = dynamic_cast<Rational*>(a.get());
        auto r2 = dynamic_cast<Rational*>(b.get());
        return RationalV(r1->numerator * r2->denominator - r2->numerator * r1->denominator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &a, const Value &b) {
    if (a->v_type == V_INT && b->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return IntegerV(n1 * n2);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_INT) {
        auto r = dynamic_cast<Rational*>(a.get());
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return RationalV(r->numerator * n2, r->denominator);
    }
    if (a->v_type == V_INT && b->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        auto r = dynamic_cast<Rational*>(b.get());
        return RationalV(n1 * r->numerator, r->denominator);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_RATIONAL) {
        auto r1 = dynamic_cast<Rational*>(a.get());
        auto r2 = dynamic_cast<Rational*>(b.get());
        return RationalV(r1->numerator * r2->numerator,
                         r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &a, const Value &b) {
    if (b->v_type == V_INT && dynamic_cast<Integer*>(b.get())->n == 0) {
        throw(RuntimeError("Division by zero"));
    }
    if (b->v_type == V_RATIONAL && dynamic_cast<Rational*>(b.get())->numerator == 0) {
        throw(RuntimeError("Division by zero"));
    }
    if (a->v_type == V_INT && b->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return RationalV(n1, n2);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_INT) {
        auto r = dynamic_cast<Rational*>(a.get());
        int n2 = dynamic_cast<Integer*>(b.get())->n;
        return RationalV(r->numerator, r->denominator * n2);
    }
    if (a->v_type == V_INT && b->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(a.get())->n;
        auto r = dynamic_cast<Rational*>(b.get());
        return RationalV(n1 * r->denominator, r->numerator);
    }
    if (a->v_type == V_RATIONAL && b->v_type == V_RATIONAL) {
        auto r1 = dynamic_cast<Rational*>(a.get());
        auto r2 = dynamic_cast<Rational*>(b.get());
        return RationalV(r1->numerator * r2->denominator,
                         r1->denominator * r2->numerator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    //TODO: To complete the addition logic
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    //TODO: To complete the substraction logic
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    //TODO: To complete the multiplication logic
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    //TODO: To complete the divisor logic
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &a, const Value &b) {
    return BooleanV(compareNumericValues(a, b) < 0);
}

Value LessEq::evalRator(const Value &a, const Value &b) {
    return BooleanV(compareNumericValues(a, b) <= 0);
}

Value Equal::evalRator(const Value &a, const Value &b) {
    return BooleanV(compareNumericValues(a, b) == 0);
}

Value GreaterEq::evalRator(const Value &a, const Value &b) {
    return BooleanV(compareNumericValues(a, b) >= 0);
}

Value Greater::evalRator(const Value &a, const Value &b) {
    return BooleanV(compareNumericValues(a, b) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    //TODO: To complete the less logic
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    //TODO: To complete the lesseq logic
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    //TODO: To complete the equal logic
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    //TODO: To complete the greatereq logic
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    //TODO: To complete the greater logic
}

Value Cons::evalRator(const Value &a, const Value &d) {
    return PairV(a, d);
}

Value ListFunc::evalRator(const std::vector<Value> &args) {
    Value lst = NullV();
    for (int i = (int)args.size() - 1; i >= 0; --i) {
        lst = PairV(args[i], lst);
    }
    return lst;
}

Value IsList::evalRator(const Value &v) {
    // proper list if Null or chain of Pairs ending in Null
    Value cur = v;
    while (cur->v_type == V_PAIR) {
        cur = dynamic_cast<Pair*>(cur.get())->cdr;
    }
    return BooleanV(cur->v_type == V_NULL);
}

Value Car::evalRator(const Value &v) {
    // DEBUG
    // std::cerr << "[DEBUG] Car arg v_type=" << v->v_type << "\n";
    if (v.get() == nullptr) throw RuntimeError("car on invalid value");
    if (v->v_type != V_PAIR) throw RuntimeError("car on non-pair");
    Pair* p = dynamic_cast<Pair*>(v.get());
    if (!p) throw RuntimeError("car on non-pair");
    return p->car;
}

Value Cdr::evalRator(const Value &v) {
    // DEBUG
    // std::cerr << "[DEBUG] Cdr arg v_type=" << v->v_type << "\n";
    if (v.get() == nullptr) throw RuntimeError("cdr on invalid value");
    if (v->v_type != V_PAIR) throw RuntimeError("cdr on non-pair");
    Pair* p = dynamic_cast<Pair*>(v.get());
    if (!p) throw RuntimeError("cdr on non-pair");
    return p->cdr;
}

Value SetCar::evalRator(const Value &pairv, const Value &newcar) {
    if (pairv->v_type != V_PAIR) throw RuntimeError("set-car! on non-pair");
    Pair* p = dynamic_cast<Pair*>(pairv.get());
    p->car = newcar;
    return VoidV();
}

Value SetCdr::evalRator(const Value &pairv, const Value &newcdr) {
    if (pairv->v_type != V_PAIR) throw RuntimeError("set-cdr! on non-pair");
    Pair* p = dynamic_cast<Pair*>(pairv.get());
    p->cdr = newcdr;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    Value last = VoidV();
    for (auto &ex : es) last = ex->eval(e);
    return last;
}

Value Quote::eval(Assoc& e) {
    if (auto num = dynamic_cast<Number*>(s.get())) return IntegerV(num->n);
    if (auto rat = dynamic_cast<RationalSyntax*>(s.get())) return RationalV(rat->numerator, rat->denominator);
    if (dynamic_cast<TrueSyntax*>(s.get())) return BooleanV(true);
    if (dynamic_cast<FalseSyntax*>(s.get())) return BooleanV(false);
    if (auto str = dynamic_cast<StringSyntax*>(s.get())) return StringV(str->s);
    if (auto sym = dynamic_cast<SymbolSyntax*>(s.get())) return SymbolV(sym->s);
    if (auto lst = dynamic_cast<List*>(s.get())) {
        if (lst->stxs.empty()) return NullV();
        // Build list from right to left
        Value result = NullV();
        for (int i = (int)lst->stxs.size() - 1; i >= 0; --i) {
            Value elem = Quote(lst->stxs[i]).eval(e);
            result = PairV(elem, result);
        }
        return result;
    }
    throw RuntimeError("Unsupported quote syntax");
}

Value AndVar::eval(Assoc &e) {
    Value last = BooleanV(true);
    for (auto &ex : rands) {
        last = ex->eval(e);
        if (last->v_type == V_BOOL && !dynamic_cast<Boolean*>(last.get())->b) return last;
    }
    return last;
}

Value OrVar::eval(Assoc &e) {
    Value last = BooleanV(false);
    for (auto &ex : rands) {
        last = ex->eval(e);
        if (!(last->v_type == V_BOOL && dynamic_cast<Boolean*>(last.get())->b == false)) return last;
    }
    return last;
}

Value Not::evalRator(const Value &v) {
    bool isFalse = (v->v_type == V_BOOL && dynamic_cast<Boolean*>(v.get())->b == false);
    return BooleanV(isFalse);
}

Value If::eval(Assoc &e) {
    Value c = cond->eval(e);
    bool truth = !(c->v_type == V_BOOL && dynamic_cast<Boolean*>(c.get())->b == false);
    if (truth) return conseq->eval(e);
    return alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    //TODO: To complete the cond logic
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value proc = rator->eval(e);
    if (proc->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}
    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc.get());

    // Evaluate arguments
    std::vector<Value> args;
    for (auto &ex : rand) args.push_back(ex->eval(e));

    // Check arity
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");

    // Build call environment: extend closure env with parameter bindings
    Assoc call_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); ++i) {
        call_env = extend(clos_ptr->parameters[i], args[i], call_env);
    }

    return clos_ptr->e->eval(call_env);
}

Value Define::eval(Assoc &env) {
    // Evaluate expression and bind globally
    Value v = e->eval(env);
    // Allow redefine
    if (find(var, env).get() != nullptr) {
        modify(var, v, env);
    } else {
        env = extend(var, v, env);
    }
    return v;
}

Value Let::eval(Assoc &env) {
    Assoc local = env;
    for (auto &p : bind) {
        Value v = p.second->eval(env);
        local = extend(p.first, v, local);
    }
    return body->eval(local);
}

Value Letrec::eval(Assoc &env) {
    Assoc env1 = env;
    for (auto &p : bind) {
        env1 = extend(p.first, Value(nullptr), env1);
    }
    // evaluate under env1
    std::vector<Value> vals;
    vals.reserve(bind.size());
    for (auto &p : bind) {
        vals.push_back(p.second->eval(env1));
    }
    Assoc env2 = env1;
    for (size_t i = 0; i < bind.size(); ++i) {
        modify(bind[i].first, vals[i], env2);
    }
    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    Value v = e->eval(env);
    modify(var, v, env);
    return v;
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
