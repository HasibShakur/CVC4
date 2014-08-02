#include "cvc4_public.h"

#ifndef __CVC4__PARSER_QUANTIFIERELIMINATE_H
#define __CVC4__PARSER_QUANTIFIERELIMINATE_H

#include<iostream>
#include<vector>
#include "expr/node.h"


namespace CVC4{
//class SmtEngine;
//namespace qe{

//attribute for "contains instantiation constants from"
struct QeNestedQuantAttributeId {};
typedef expr::Attribute<QeNestedQuantAttributeId, Node> QeNestedQuantAttribute;

class CVC4_PUBLIC QuantifierEliminate {
private:
  CVC4::Expr expression;
  CVC4::Node convertToPrenex(CVC4::Node body,std::vector< CVC4::Node >& args, bool pol);
  void setNestedQuantifiers( CVC4::Node n, CVC4::Node q );
  void setNestedQuantifiers2( CVC4::Node n, CVC4::Node q, std::vector< CVC4::Node >& processed );
  //void setAttribute(CVC4::Node in, CVC4::Node n);
  CVC4::Node convertToNNF(CVC4::Node body);
  bool isLiteral(CVC4::Node n);
public:
  QuantifierEliminate();
  ~QuantifierEliminate();
  CVC4::Expr getExpression();
  void setExpression(const Expr& e);
  CVC4::Node getPrenexExpression(const Expr& e);
  CVC4::Node simplifyExpression(const Expr& e);
};
}
//}
//}

#endif
