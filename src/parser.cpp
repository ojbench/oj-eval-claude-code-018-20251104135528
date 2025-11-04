/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 *
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    // check if the first element is a symbol
    // If not, use Apply function to package to a closure;
    // If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // If not a symbol, treat first element as operator expression and rest as arguments
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); ++i) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), args));
    } else {
        string op = id->s;

        // If operator is a variable in current env -> apply that variable
        if (find(op, env).get() != nullptr) {
            vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); ++i) {
                parameters.push_back(stxs[i]->parse(env));
            }
            // Variable application: (op args...)
            return Expr(new Apply(Expr(new Var(op)), parameters));
        }

        // Primitive operations -> construct concrete Exprs
        if (primitives.count(op) != 0) {
            vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); ++i) {
                parameters.push_back(stxs[i]->parse(env));
            }

            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                if (parameters.size() == 2) {
                    return Expr(new Plus(parameters[0], parameters[1]));
                } else {
                    throw RuntimeError("Wrong number of arguments for +");
                }
            } else if (op_type == E_MINUS) {
                if (parameters.size() == 2) return Expr(new Minus(parameters[0], parameters[1]));
                throw RuntimeError("Wrong number of arguments for -");
            } else if (op_type == E_MUL) {
                if (parameters.size() == 2) return Expr(new Mult(parameters[0], parameters[1]));
                throw RuntimeError("Wrong number of arguments for *");
            }  else if (op_type == E_DIV) {
                if (parameters.size() == 2) return Expr(new Div(parameters[0], parameters[1]));
                throw RuntimeError("Wrong number of arguments for /");
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for modulo");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_CONS) {
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for cons");
                return Expr(new Cons(parameters[0], parameters[1]));
            } else if (op_type == E_CAR) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for car");
                return Expr(new Car(parameters[0]));
            } else if (op_type == E_CDR) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for cdr");
                return Expr(new Cdr(parameters[0]));
            } else if (op_type == E_SETCAR) {
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-car!");
                return Expr(new SetCar(parameters[0], parameters[1]));
            } else if (op_type == E_SETCDR) {
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for set-cdr!");
                return Expr(new SetCdr(parameters[0], parameters[1]));
            } else if (op_type == E_NOT) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for not");
                return Expr(new Not(parameters[0]));
            } else if (op_type == E_DISPLAY) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for display");
                return Expr(new Display(parameters[0]));
            } else if (op_type == E_EQQ) {
                if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for eq?");
                return Expr(new IsEq(parameters[0], parameters[1]));
            } else if (op_type == E_BOOLQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for boolean?");
                return Expr(new IsBoolean(parameters[0]));
            } else if (op_type == E_INTQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for number?");
                return Expr(new IsFixnum(parameters[0]));
            } else if (op_type == E_NULLQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for null?");
                return Expr(new IsNull(parameters[0]));
            } else if (op_type == E_PAIRQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for pair?");
                return Expr(new IsPair(parameters[0]));
            } else if (op_type == E_PROCQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for procedure?");
                return Expr(new IsProcedure(parameters[0]));
            } else if (op_type == E_SYMBOLQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for symbol?");
                return Expr(new IsSymbol(parameters[0]));
            } else if (op_type == E_LISTQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for list?");
                return Expr(new IsList(parameters[0]));
            } else if (op_type == E_STRINGQ) {
                if (parameters.size() != 1) throw RuntimeError("Wrong number of arguments for string?");
                return Expr(new IsString(parameters[0]));
            } else {
                // Default: treat as Apply of operator symbol
                vector<Expr> params;
                for (size_t i = 1; i < stxs.size(); ++i) params.push_back(stxs[i]->parse(env));
                return Expr(new Apply(Expr(new Var(op)), params));
            }
        }

        // Reserved words (special forms)
        if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
                case E_BEGIN: {
                    std::vector<Expr> seq;
                    for (size_t i = 1; i < stxs.size(); ++i) seq.push_back(stxs[i]->parse(env));
                    return Expr(new Begin(seq));
                }
                case E_QUOTE: {
                    if (stxs.size() != 2) throw RuntimeError("Wrong number of arguments for quote");
                    return Expr(new Quote(stxs[1]));
                }
                case E_IF: {
                    if (stxs.size() != 4) throw RuntimeError("Wrong number of arguments for if");
                    return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
                }
                case E_LAMBDA: {
                    // (lambda (params...) body)
                    if (stxs.size() < 3) throw RuntimeError("Wrong number of arguments for lambda");
                    List* plist = dynamic_cast<List*>(stxs[1].get());
                    if (!plist) throw RuntimeError("lambda params must be a list");
                    std::vector<std::string> params;
                    for (auto &p : plist->stxs) {
                        SymbolSyntax* sid = dynamic_cast<SymbolSyntax*>(p.get());
                        if (!sid) throw RuntimeError("lambda param must be symbol");
                        params.push_back(sid->s);
                    }
                    // body is single expression for now
                    Expr body = stxs[2]->parse(env);
                    return Expr(new Lambda(params, body));
                }
                case E_DEFINE: {
                    if (stxs.size() != 3) throw RuntimeError("Wrong number of arguments for define");
                    SymbolSyntax* name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!name) throw RuntimeError("define variable must be symbol");
                    return Expr(new Define(name->s, stxs[2]->parse(env)));
                }
                case E_LET: {
                    // (let ((p v)...) body)
                    if (stxs.size() < 3) throw RuntimeError("Wrong number of arguments for let");
                    List* binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds) throw RuntimeError("let bindings must be list");
                    std::vector<std::pair<std::string, Expr>> vec;
                    for (auto &b : binds->stxs) {
                        List* pairlst = dynamic_cast<List*>(b.get());
                        if (!pairlst || pairlst->stxs.size() != 2) throw RuntimeError("let binding must be (name expr)");
                        SymbolSyntax* sid = dynamic_cast<SymbolSyntax*>(pairlst->stxs[0].get());
                        if (!sid) throw RuntimeError("let binding name must be symbol");
                        vec.push_back({sid->s, pairlst->stxs[1]->parse(env)});
                    }
                    Expr body = stxs[2]->parse(env);
                    return Expr(new Let(vec, body));
                }
                case E_LETREC: {
                    // same parsing as let
                    if (stxs.size() < 3) throw RuntimeError("Wrong number of arguments for letrec");
                    List* binds = dynamic_cast<List*>(stxs[1].get());
                    if (!binds) throw RuntimeError("letrec bindings must be list");
                    std::vector<std::pair<std::string, Expr>> vec;
                    for (auto &b : binds->stxs) {
                        List* pairlst = dynamic_cast<List*>(b.get());
                        if (!pairlst || pairlst->stxs.size() != 2) throw RuntimeError("letrec binding must be (name expr)");
                        SymbolSyntax* sid = dynamic_cast<SymbolSyntax*>(pairlst->stxs[0].get());
                        if (!sid) throw RuntimeError("letrec binding name must be symbol");
                        vec.push_back({sid->s, pairlst->stxs[1]->parse(env)});
                    }
                    Expr body = stxs[2]->parse(env);
                    return Expr(new Letrec(vec, body));
                }
                case E_SET: {
                    if (stxs.size() != 3) throw RuntimeError("Wrong number of arguments for set!");
                    SymbolSyntax* name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                    if (!name) throw RuntimeError("set! target must be symbol");
                    return Expr(new Set(name->s, stxs[2]->parse(env)));
                }
                case E_COND: {
                    // (cond (pred expr...) ... (else expr...))
                    std::vector<std::vector<Expr>> clauses;
                    for (size_t i = 1; i < stxs.size(); ++i) {
                        List* clause = dynamic_cast<List*>(stxs[i].get());
                        if (!clause || clause->stxs.size() == 0) throw RuntimeError("cond clause must be a list");
                        std::vector<Expr> ce;
                        for (auto &citem : clause->stxs) {
                            ce.push_back(citem->parse(env));
                        }
                        clauses.push_back(ce);
                    }
                    return Expr(new Cond(clauses));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
            }
        }

        // default: use Apply to be an expression
        std::vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(Expr(new Var(op)), parameters));
    }
}
