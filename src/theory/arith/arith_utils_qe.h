#ifndef __CVC4__EXPR__ARITH__UTILS_QE_H
#define __CVC4__EXPR__ARITH__UTILS_QE_H

#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "util/rational.h"


namespace CVC4{
namespace theory {
namespace arith {

class NodeWrapperQE {
private:
  Node node;
public:
  NodeWrapperQE(Node n) : node(n) {}
  const Node& getNodeQE() const { return node; }
};


class ConstantQE : public NodeWrapperQE {
public:
  ConstantQE(Node n) : NodeWrapperQE(n) {
    Assert(isMemberQE(getNodeQE()));
  }

  static bool isMemberQE(Node n) {
    return n.getKind() == kind::CONST_RATIONAL;
  }
 static ConstantQE mkConstantQE(Node n) {
    Assert(n.getKind() == kind::CONST_RATIONAL);
    return ConstantQE(n);
  }

  static ConstantQE mkConstantQE(const Rational& rat);

  static ConstantQE mkZeroQE() {
    return mkConstantQE(Rational(0));
  }

  static ConstantQE mkOneQE() {
    return mkConstantQE(Rational(1));
  }

  const Rational& getValueQE() const {
    return getNodeQE().getConst<Rational>();
  }

  static int absCmpQE(const ConstantQE& a, const ConstantQE& b);
  bool isIntegralQE() const { return getValueQE().isIntegral() ;}

  int sgnQE() const { return getValueQE().sgn(); }

  bool isZeroQE() const { return sgnQE() == 0; }
  bool isNegativeQE() const { return sgnQE() < 0; }
  bool isPositiveQE() const { return sgnQE() > 0; }

  bool isOneQE() const { return getValueQE() == 1; }

  ConstantQE operator*(const Rational& other) const {
    return mkConstantQE(getValueQE() * other);
  }

  ConstantQE operator*(const ConstantQE& other) const {
    return mkConstantQE(getValueQE() * other.getValueQE());
  }
  ConstantQE operator+(const ConstantQE& other) const {
    return mkConstantQE(getValueQE() + other.getValueQE());
  }
  ConstantQE operator-() const {
    return mkConstantQE(-getValueQE());
  }

  ConstantQE inverseQE() const{
    Assert(!isZeroQE());
    return mkConstantQE(getValueQE().inverse());
  }

  bool operator<(const ConstantQE& other) const {
    return getValueQE() < other.getValueQE();
  }

  bool operator==(const ConstantQE& other) const {
    //Rely on node uniqueness.
    return getNodeQE() == other.getNodeQE();
  }

  ConstantQE absQE() const {
    if(isNegativeQE()){
      return -(*this);
    }else{
      return (*this);
    }
  }

  uint32_t lengthQE() const{
    Assert(isIntegralQE());
    return getValueQE().getNumerator().length();
  }
};/* class Constant */

/*class VariableQE : public NodeWrapperQE {
public:
  VariableQE(Node n) : NodeWrapperQE(n) {
    Assert(isMemberQE(getNodeQE()));
  }

  // TODO: check if it's a theory leaf also
  static bool isMemberQE(Node n) {
    Kind k = n.getKind();
    switch(k){
    case kind::CONST_RATIONAL:
      return false;
    case kind::INTS_DIVISION:
    case kind::INTS_MODULUS:
    case kind::DIVISION:
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
    case kind::DIVISION_TOTAL:
      return isDivMemberQE(n);
    case kind::ABS:
    case kind::TO_INTEGER:
      // Treat to_int as a variable; it is replaced in early preprocessing
      // by a variable.
      return true;
    default:
      return isLeafMemberQE(n);
    }
  }

  static bool isLeafMemberQE(Node n);
  static bool isDivMemberQE(Node n);
  bool isDivLikeQE() const{
    return isDivMemberQE(getNodeQE());
  }

  bool isIntegralQE() const {
    return getNodeQE().getType().isInteger();
  }

  bool isMetaKindVariableQE() const {
    return getNodeQE().isVar();
  }

  bool operator<(const VariableQE& v) const {
    VariableNodeCmpQE cmp;
    return cmp(this->getNodeQE(), v.getNodeQE());

    // bool thisIsVariable = isMetaKindVariable();
    // bool vIsVariable = v.isMetaKindVariable();

    // if(thisIsVariable == vIsVariable){
    //   bool thisIsInteger = isIntegral();
    //   bool vIsInteger = v.isIntegral();
    //   if(thisIsInteger == vIsInteger){
    //     return getNode() < v.getNode();
    //   }else{
    //     return thisIsInteger && !vIsInteger;
    //   }
    // }else{
    //   return thisIsVariable && !vIsVariable;
    // }
  }

  struct VariableNodeCmpQE {
    bool operator()(Node n, Node m) const {
      bool nIsVariable = n.isVar();
      bool mIsVariable = m.isVar();

      if(nIsVariable == mIsVariable){
        bool nIsInteger = n.getType().isInteger();
        bool mIsInteger = m.getType().isInteger();
        if(nIsInteger == mIsInteger){
          return n < m;
        }else{
          return nIsInteger && !mIsInteger;
        }
      }else{
        return nIsVariable && !mIsVariable;
      }
    }
  };

  bool operator==(const VariableQE& v) const { return getNodeQE() == v.getNodeQE();}
}; class Variable */

}
}
};
#endif
