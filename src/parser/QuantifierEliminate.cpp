#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/expr_template.h"
#include "parser/QuantifierEliminate.h"
#include "parser/input.h"
#include "parser/parser.h"
using namespace std;
using namespace CVC4;
using namespace CVC4::kind;

QuantifierEliminate::QuantifierEliminate(const CVC4::Expr& ex) {
  this->expression = ex;
}
QuantifierEliminate::~QuantifierEliminate() {
}
CVC4::Expr QuantifierEliminate::getExpression() {
  return this->expression;
}
/*QuantifierEliminate::void parseQuantifiers(const CVC4::Expr& ex)
 {
 Node tempBody = Node::fromExpr(ex);
 for(size_t i= 0;i<tempBody[0].getNumChildren();i++)
 {
 if(tempBody[0][i].getKind() == kind::FORALL || tempBody[0][i].getKind() == kind::EXISTS )
 {
 d_quants.push_back(tempBody[0][i].getType());
 }
 }
 }
 QuantifierEliminate::int getNumQuantifiers()
 {
 return (int)d_quants.size();
 }
 QuantifierEliminate::Node getQuantifier( int i )
 {
 return this->d_quants[i];
 }*/
CVC4::Expr QuantifierEliminate::getPrenexExpression(const CVC4::Expr& ex) {
  Node body = Node::fromExpr(ex);
  std::vector< Node > args;
  if( body.getKind()==kind::EXISTS || body.getKind()==kind::FORALL ){
      //Trace("quantifiers-rewrite-debug") << "pre-rewriting " << body << " " << body[0].hasAttribute(NestedQuantAttribute()) << std::endl;
      if( !body.hasAttribute(NestedQuantAttribute()) ){
        setNestedQuantifiers( body[ 1 ], body );
      }
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
  }
  Node prenexedBody = computePrenex(body, args, true);
  CVC4::Expr prenexedExpr = prenexedBody.toExpr();
  return prenexedExpr;
}
Node QuantifierEliminate::computePrenex(Node body,std::vector< Node >& args, bool pol) {
if(body.getKind() == kind::FORALL)
{
  std::vector<Node> terms;
  std::vector<Node> subs;
  //for doing prenexing of same-signed quantifiers
  //must rename each variable that already exists
  for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
    terms.push_back(body[0][i]);
    subs.push_back(NodeManager::currentNM()->mkBoundVar(body[0][i].getType()));
  }
  args.insert( args.end(), subs.begin(), subs.end() );
  Node newBody = body[1];
  newBody = newBody.substitute(terms.begin(), terms.end(), subs.begin(), subs.end());
  //Debug("quantifiers-substitute-debug") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << endl;
  return newBody;
} else {
  Assert( body.getKind()!=kind::EXISTS );
  bool childrenChanged = false;
  std::vector<Node> newChildren;
  for(int i = 0; i < (int) body.getNumChildren(); i++) {
    bool newPol = body.getKind() == kind::NOT ? !pol : pol;
    Node n = computePrenex(body[i], args, newPol);
    newChildren.push_back(n);
    if(n != body[i]) {
      childrenChanged = true;
    }
  }
  if(childrenChanged) {
    if(body.getKind() == kind::NOT && newChildren[0].getKind() == kind::NOT) {
      return newChildren[0][0];
    } else {
      return NodeManager::currentNM()->mkNode(body.getKind(), newChildren);
    }
  } else {
    return body;
  }
}
}
void QuantifierEliminate::setNestedQuantifiers( Node n, Node q ){
  std::vector< Node > processed;
  setNestedQuantifiers2( n, q, processed );
}

void QuantifierEliminate::setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed ) {
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
    processed.push_back( n );
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
      NestedQuantAttribute nqai;
      n[0].setAttribute(nqai,q);
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setNestedQuantifiers2( n[i], q, processed );
    }
  }
}
