#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"
#include "util/integer.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace std;

int main() {
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);
  //SmtEngine smt2(&em);
  smt.setLogic("LIA");
  smt.setOption("produce-models", true);
 // smt.setOption("finite-model-find", true);
  Type integer = em.integerType();
  Expr y = em.mkVar("y",integer);
  Expr x = em.mkVar("x",integer);
  Expr two = em.mkConst(Rational(2));
  Expr two_x = em.mkExpr(kind::MULT,two,x);
  Expr exp1 = em.mkExpr(kind::EQUAL,y,two_x);
  Result r1 = smt.checkSat(exp1);
  std::cout<<"x => "<<smt.getValue(x)<<std::endl;
  std::cout<<"y => "<<smt.getValue(y)<<std::endl;
  SmtEngine smt2(&em);
  smt2.setLogic("LIA");
  smt2.setOption("produce-models", true);
  Expr y1 = em.mkVar("y",integer);
  Expr x1 = em.mkVar("x",integer);
  Expr ex1 = em.mkExpr(kind::PLUS,x1,smt.getValue(x));
  Expr ex2 = em.mkExpr(kind::PLUS,y1,smt.getValue(y));
  Expr ex3 = em.mkExpr(kind::AND,ex1,ex2);
  Expr ex4 = em.mkExpr(kind::EQUAL,ex2,em.mkConst(Rational(0)));
  Expr final = em.mkExpr(kind::EQUAL,ex4,exp1);
  Result r2 = smt2.query(final);
  std::cout<<"final "<<r2.toString()<<std::endl;

  //Result r = smt.query(em.mkConst(true));
  //Result r2 = smt2.query(em.mkConst(true));

 // return r == Result::VALID && r2 == Result::VALID ? 0 : 1;
  return 0;
}
