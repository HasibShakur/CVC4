//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "parser/QuantifierEliminate.h"
#include "expr/attribute.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;

//attribute for "contains instantiation constants from"
/*struct QeNestedQuantAttributeId {};
typedef CVC4::expr::Attribute<QeNestedQuantAttributeId,CVC4::TNode> QuantAttrib;*/

Node QuantifierEliminate::convertToPrenex(Node body, std::vector< Node >& args, bool pol)
{
  if( body.getKind()==FORALL ){
      if( pol ){
        std::vector< Node > terms;
        std::vector< Node > subs;
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
          terms.push_back( body[0][i] );
          subs.push_back( NodeManager::currentNM()->mkBoundVar( body[0][i].getType() ) );
        }
        args.insert( args.end(), subs.begin(), subs.end() );
        Node newBody = body[1];
        newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
        Debug("quantifiers-substitute-debug") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << endl;
        return newBody;
      }else{
        return body;
      }
    }else if( body.getKind()==ITE || body.getKind()==XOR || body.getKind()==IFF ){
      return body;
    }else{
      Assert( body.getKind()!=EXISTS );
      bool childrenChanged = false;
      std::vector< Node > newChildren;
      for( int i=0; i<(int)body.getNumChildren(); i++ ){
        bool newPol = body.getKind()==NOT  ? !pol : pol;
        Node n = convertToPrenex( body[i], args, newPol );
        newChildren.push_back( n );
        if( n!=body[i] ){
          childrenChanged = true;
        }
      }
      if( childrenChanged ){
        if( body.getKind()==NOT && newChildren[0].getKind()==NOT ){
          return newChildren[0][0];
        }else{
          return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
        }
      }else{
        return body;
      }
    }
}
Node QuantifierEliminate::getPrenexExpression(Node f)
{
  if( f.getKind()==FORALL ){
      Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << ", nested = " << isNested << std::endl;
      std::vector< Node > args;
      for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
        args.push_back( f[0][i] );
     }
    Node n = f[1];
    n = convertToPrenex(n,args, true);
    return n;
  }
  else
  {
    return f;
  }
}

/*
//attribute for "contains nested quantifier"
struct QeContainsQuantifierAttributeId {};
typedef CVC4::expr::Attribute<QeContainsQuantifierAttributeId,uint64_t> ContainsQuantAttrib;

bool QuantifierEliminate::containsQuantifierQe(CVC4::Node n)
{
  if( n.hasAttribute(ContainsQuantAttrib()) ){
      return n.getAttribute(ContainsQuantAttrib())==1;
    } else if(n.getKind() == kind::FORALL || n.getKind() == kind::EXISTS ) {
      return true;
    } else {
      bool cq = false;
      for( unsigned i = 0; i < n.getNumChildren(); ++i ){
        if( containsQuantifierQe(n[i]) ){
          cq = true;
          break;
        }
      }
      ContainsQuantAttrib quantAttrib;
      n.setAttribute(quantAttrib, cq ? 1 : 0);
      return cq;
    }
}


void QuantifierEliminate::setNestedQuantifiers( CVC4::Node n, CVC4::Node q ){
  std::vector< CVC4::Node > processed;
  setNestedQuantifiersInner( n, q, processed );
}

void QuantifierEliminate::setNestedQuantifiersInner(CVC4::Node n, CVC4::Node q, std::vector<CVC4::Node>& processed)
{
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
     processed.push_back( n );
     if( n.getKind()== FORALL || n.getKind()==EXISTS ){
       Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
       QuantAttrib qa;
       n[0].setAttribute(qa,q);
     }
     for( int i=0; i<(int)n.getNumChildren(); i++ ){
       setNestedQuantifiersInner( n[i], q, processed );
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
    return n[0].getType()!=CVC4::NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}

CVC4::TNode QuantifierEliminate::convertToPrenex(CVC4::TNode body,std::vector< CVC4::TNode >& args, bool pol) {
  if(body.getKind() == kind::FORALL)
  {
    std::vector<CVC4::TNode> terms;
    std::vector<CVC4::TNode> subs;
    //for doing prenexing of same-signed quantifiers
    //must rename each variable that already exists
    for(int i = 0; i < (int) body[0].getNumChildren(); i++) {
      terms.push_back(body[0][i]);
      subs.push_back(CVC4::NodeManager::currentNM()->mkBoundVar(body[0][i].getType()));
    }
    args.insert( args.end(), subs.begin(), subs.end() );
    CVC4::TNode newBody = body[1];
    newBody = newBody.substitute(terms.begin(), terms.end(), subs.begin(), subs.end());
    return newBody;
  }
  else if( body.getKind()==kind::ITE || body.getKind()==kind::XOR || body.getKind()== kind::IFF )
  {
    return body;
  }
  else
  {
    Assert( body.getKind()!=kind::EXISTS );
    bool childrenChanged = false;
    std::vector<CVC4::TNode> newChildren;
    for(int i = 0; i < (int) body.getNumChildren(); i++) {
      bool newPol = body.getKind() == kind::NOT ? !pol : pol;
      CVC4::Node n = convertToPrenex(body[i], args, newPol);
      newChildren.push_back(n);
      if(n != body[i]) {
        childrenChanged = true;
      }
    }
    if(childrenChanged) {
      if(body.getKind() == kind::NOT && newChildren[0].getKind() == kind::NOT) {
        return newChildren[0][0];
      } else {
        return CVC4::NodeManager::currentNM()->mkNode(body.getKind(), newChildren);
      }
    } else {
      return body;
    }
  }
}
CVC4::Node QuantifierEliminate::convertToNNF(CVC4::Node body)
{
  if( body.getKind()== kind::NOT ){
    if( body[0].getKind()== kind::NOT ){
      return convertToNNF( body[0][0] );
    }else if( isLiteral( body[0] ) ){
      return body;
    }else{
      std::vector< CVC4::Node > children;
      Kind k = body[0].getKind();
      if( body[0].getKind()== kind::OR || body[0].getKind()== kind::AND ){
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          children.push_back( convertToNNF( body[0][i].noNode() ) );
        }
        k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
      }else if( body[0].getKind()== kind::IFF ){
        for( int i=0; i<2; i++ ){
          CVC4::Node nn = i==0 ? body[0][i] : body[0][i].noNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else if( body[0].getKind()== kind::ITE ){
        for( int i=0; i<3; i++ ){
          CVC4::Node nn = i==0 ? body[0][i] : body[0][i].noNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else{
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return CVC4::NodeManager::currentNM()->mkNode( k, children );
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
      return CVC4::NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
}
CVC4::Node QuantifierEliminate::normalizeBody(CVC4::Node body)
{
  bool rewritten = false;
  CVC4::Node normalized;
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
      if(this->isLiteral(body[i]))
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
}
CVC4::TNode QuantifierEliminate::getPrenexExpression(const Expr& ex) {
  CVC4::TNode tBody = CVC4::NodeTemplate<false>(ex);
  std::vector< CVC4::TNode > args;
  CVC4::TNode tn  = tBody;
  for(int i=0;i<(int)tBody[0].getNumChildren();i++)
  {
    args.push_back( tBody[0][i] );
  }
  CVC4::TNode ipl_temp = tBody[2];
  if( tBody.getKind()==CVC4::kind::EXISTS){
        std::vector< TNode > children;
        children.push_back( tBody[0] );
        children.push_back( tBody[1].negate() );
        if( tBody.getNumChildren()==3 ){
          children.push_back( tBody[2] );
        }
        tn = NodeManager::currentNM()->mkNode( CVC4::kind::FORALL, children );
        tn = tn.negate();
        bool isNested = tBody[0].hasAttribute(QuantAttrib());
        tn = computePrenexOperation( tBody, isNested );
        return tn;
      }
  else{
        bool isNested = tBody[0].hasAttribute(QuantAttrib());
        //doOperation( in, isNested, op );
        tn = computePrenexOperation( tBody, isNested );
        return tn;
      }
}
CVC4::TNode QuantifierEliminate::computePrenexOperation(CVC4::TNode in, bool isNested)
{
  if( in.getKind()==CVC4::kind::FORALL ){
      std::vector< CVC4::TNode > args;
      for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
        args.push_back( in[0][i] );
      }
      CVC4::NodeBuilder<> defs(kind::AND);
      CVC4::TNode n = in[1];
      CVC4::TNode ipl;
      if( in.getNumChildren()==3 ){
        ipl = in[2];
      }
      //n = convertToPrenex( n, args, true );
       n = convertToPrenex(n,args, true);
      if( in[1]==n && args.size()==in[0].getNumChildren() ){
        return in;
      }else{
        if( args.empty() ){
          defs << n;
        }else{
          std::vector< CVC4::TNode > children;
          children.push_back( CVC4::NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
          children.push_back( n );
          if( !ipl.isNull() ){
            children.push_back( ipl );
          }
          defs << CVC4::NodeManager::currentNM()->mkNode(kind::FORALL, children );
        }
        return defs.getNumChildren()==1 ? defs.getChild( 0 ) : defs.constructNode();
      }
    }else{
      return in;
    }
}
CVC4::Node QuantifierEliminate::simplifyExpression(const Expr& ex)
{
  // 1st phase of simplification is converting the expression to NNF
  CVC4::Node temp = CVC4::Node::fromExpr(ex);
  CVC4::Node nnfNode = convertToNNF(temp);
  // 3rd phase of simplification is applying the replace rules
  //Node normalizedBody = normalizeBody(nnfNode);
  // 4th phase of simplification is
  return nnfNode;
}
*/
