#include "expr/arith_utils_qe.h"
#include "theory/arith/arith_utilities.h"
#include <list>
#include "theory/theory.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::theory::arith;

ConstantQE ConstantQE::mkConstantQE(const Rational& rat) {
  return ConstantQE(mkRationalNode(rat));
}

/*bool VariableQE::isLeafMemberQE(Node n)
{
  return (!QuantifierEliminate::isRelationalOperatorTypeQE(n.getKind())) &&
      (Theory::isLeafOf(n, theory::THEORY_ARITH));
}

bool VariableQE::isDivMemberQE(Node n)
{
  switch(n.getKind()){
    case kind::DIVISION:
    case kind::INTS_DIVISION:
    case kind::INTS_MODULUS:
    case kind::DIVISION_TOTAL:
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
      return Polynomial::isMember(n[0]) && Polynomial::isMember(n[1]);
    default:
      return false;
}*/
