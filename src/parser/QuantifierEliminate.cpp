//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "parser/QuantifierEliminate.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;

QuantifierEliminate::QuantifierEliminate() {}
void QuantifierEliminate::setExpression(const Expr& e)
{
  this->expression = e;
}
CVC4::Expr QuantifierEliminate::getExpression()
{
   return this->expression;
}
void QuantifierEliminate::setNestedQuantifiers( CVC4::Node n, CVC4::Node q ){
  std::vector< CVC4::Node > processed;
  setNestedQuantifiers2( n, q, processed );
}

void QuantifierEliminate::setNestedQuantifiers2( CVC4::Node n, CVC4::Node q, std::vector< CVC4::Node >& processed ) {
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
    processed.push_back( n );
    if( n.getKind()== FORALL || n.getKind()==EXISTS ){
      Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
      QeNestedQuantAttributeId nqai;
      n[0].setAttribute(nqai,q);
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
	setNestedQuantifiers2( n[i], q, processed );
    }
  }
}

bool QuantifierEliminate::isLiteral( CVC4::Node n ){
  switch( n.getKind() ){
  case NOT:
    return isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
  case IFF:
    return false;
    break;
  case EQUAL:
    return n[0].getType()!=NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}
Node QuantifierEliminate::convertToPrenex(CVC4::Node body,std::vector< CVC4::Node >& args, bool pol) {
if(body.getKind() == FORALL)
{
  std::vector<CVC4::Node> terms;
  std::vector<CVC4::Node> subs;
  //for doing prenexing of same-signed quantifiers
  //must rename each variable that already exists
  for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
    terms.push_back(body[0][i]);
    subs.push_back(NodeManager::currentNM()->mkBoundVar(body[0][i].getType()));
  }
  args.insert( args.end(), subs.begin(), subs.end() );
  CVC4::Node newBody = body[1];
  newBody = newBody.substitute(terms.begin(), terms.end(), subs.begin(), subs.end());
  //Debug("quantifiers-substitute-debug") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << endl;
  return newBody;
} else {
  Assert( body.getKind()!=EXISTS );
  bool childrenChanged = false;
  std::vector<CVC4::Node> newChildren;
  for(int i = 0; i < (int) body.getNumChildren(); i++) {
    bool newPol = body.getKind() == NOT ? !pol : pol;
    CVC4::Node n = this->convertToPrenex(body[i], args, newPol);
    newChildren.push_back(n);
    if(n != body[i]) {
      childrenChanged = true;
    }
  }
  if(childrenChanged) {
    if(body.getKind() == NOT && newChildren[0].getKind() == NOT) {
      return newChildren[0][0];
    } else {
      return NodeManager::currentNM()->mkNode(body.getKind(), newChildren);
    }
  } else {
    return body;
  }
}
}
CVC4::Node QuantifierEliminate::convertToNNF(CVC4::Node body)
{
  if( body.getKind()==NOT ){
    if( body[0].getKind()==NOT ){
      return convertToNNF( body[0][0] );
    }else if( isLiteral( body[0] ) ){
      return body;
    }else{
      std::vector< CVC4::Node > children;
      Kind k = body[0].getKind();
      if( body[0].getKind()==OR || body[0].getKind()==AND ){
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          children.push_back( convertToNNF( body[0][i].notNode() ) );
        }
        k = body[0].getKind()==AND ? OR : AND;
      }else if( body[0].getKind()==IFF ){
        for( int i=0; i<2; i++ ){
          CVC4::Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else if( body[0].getKind()==ITE ){
        for( int i=0; i<3; i++ ){
          CVC4::Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else{
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode( k, children );
    }
  }else if( isLiteral( body ) ){
    return body;
  }else{
    std::vector< CVC4::Node > children;
    bool childrenChanged = false;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      CVC4::Node nc = convertToNNF( body[i] );
      children.push_back( nc );
      childrenChanged = childrenChanged || nc!=body[i];
    }
    if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
}
/*Node normalizeBody(Node body)
{
  bool rewritten = false;
  Node normalized;
  for(int i=0;i<(int)body.getNumChildren();i++)
  {
    if(body[i].getKind() == NOT)
    {
      //If it is not then do the normalization of the expression whose kind is not
      //Just call the negateNode on the simplification done on the else part
    }
    else
    {
      // If it is not of the kind not then directly normalize this
      if(QuantifiersRewriter::isLiteral(body[i]))
      {
        // If it is a literal then we need to do nothing
        rewritten = false;
      }
      else if(body[i].getKind()==EQUAL)
      {
      //  body[i].kinded_iterator::begin(body[i],EQUAL);
      }
      // If the operator is > then convert it to < by just exchanging the operators then making a node using mkNode
      // If the operator is = then use the following conversion s=t <==> s>t+1 and t>s+1
    }
  }
  if(!rewritten)
  {
    return body;
  }
  else
  {
    return normalized;
  }
}*/
/*Node QuantifierEliminate::replaceUniversal(Node body)
{
   if(body.getKind() == kind::FORALL)
   {
	
   }
}*/
CVC4::Node QuantifierEliminate::getPrenexExpression(const Expr& ex) {
  CVC4::Node body = CVC4::Node::fromExpr(ex);
  std::vector< CVC4::Node > args;
  if( body.getKind()==EXISTS || body.getKind()==FORALL ){
//      Trace("quantifiers-eliminate-debug") << "pre-rewriting " << body << " " << body[0].hasAttribute(NestedQuantAttribute()) << std::endl;
    if( !body.hasAttribute(QeNestedQuantAttribute()) ){
         setNestedQuantifiers( body[ 1 ], body );
      }
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
  }
  CVC4::Node prenexedBody = this->convertToPrenex(body[1], args, true);
  this->setExpression(prenexedBody.toExpr());
  return prenexedBody;
}
CVC4::Node QuantifierEliminate::simplifyExpression(const Expr& ex)
{
  // 1st phase of simplification is converting the expression to NNF
  CVC4::Node temp = CVC4::Node::fromExpr(this->getExpression());
  CVC4::Node nnfNode = this->convertToNNF(temp);
  // 2nd phase of simplification is replacing universal quantifiers with existential quantifiers
 // Node allExistentialNode = replaceUniversal(nnfNode);
  // 3rd phase of simplification is applying the replace rules
  //Node normalizedBody = normalizeBody(nnfNode);
  // 4th phase of simplification is
  this->setExpression(nnfNode.toExpr());
  return nnfNode;
}
QuantifierEliminate::~QuantifierEliminate() {}
