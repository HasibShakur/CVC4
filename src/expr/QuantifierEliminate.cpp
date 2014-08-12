//#include "cvc4_public.h"

#include<iostream>
#include<vector>
#include "expr/node.h"
#include "expr/QuantifierEliminate.h"
#include "expr/attribute.h"
#include "printer/smt2/smt2_printer.h"
#include "util/output.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::printer;

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
        if(newBody.isNull())
        {
          Debug("expr-quantifiereliminate") << "newBody is null in convertToPrenex" << "\n" ;
        }
        Debug("expr-quantifiereliminate") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << "\n";
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
Node QuantifierEliminate::convertExistentialToForAll(Node f)
{
   Node ret =f;
   if( f.getKind()==EXISTS ){
     std::vector< Node > children;
     children.push_back( f[0] );
     children.push_back( f[1].negate() );
     if( f.getNumChildren()==3 ){
       children.push_back( f[2] );
     }
     ret = NodeManager::currentNM()->mkNode( FORALL, children );
     ret = ret.negate();
     if(ret.isNull())
     {
       Debug("expr-quantifiereliminate") << "ret is null after conversion from existential to forall" << "\n";
     }
     return ret;
   }
   else
   {
     return f;
   }
}
Node QuantifierEliminate::getPrenexExpression(Node f)
{
   Node in = convertExistentialToForAll(f);
   if( in.getKind()==FORALL ){
    //  Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << ", nested = " << isNested << std::endl;
      std::vector< Node > args;
      for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
        args.push_back( in[0][i] );
     }
    Node n = in[1];
    if(n.isNull())
    {
      Debug("expr-quantifiereliminate") << "Node n is null in getPrenexExpression after Node n = in[1]" << "\n";
    }
    n = convertToPrenex(n,args, true);
    if(n.isNull())
    {
      Debug("expr-quantifiereliminate") << "Node n is null in getPrenexExpression after Node n = n = convertToPrenex(n,args, true)" << "\n";
    }
    return n;
  }
  else
  {
    return in;
  }
}

/*bool QuantifierEliminate::isLiteral( Node n ){
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
    return n[0].getType()!= NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}*/

/*Node QuantifierEliminate::convertToNNF(Node body)
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
          children.push_back( convertToNNF( body[0][i].notNode() ) );
        }
        k = body[0].getKind()== kind::AND ? kind::OR : kind::AND;
      }else if( body[0].getKind()== kind::IFF ){
        for( int i=0; i<2; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( convertToNNF( nn ) );
        }
      }else if( body[0].getKind()== kind::ITE ){
        for( int i=0; i<3; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
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
      Node nc = convertToNNF( body[i] );
      children.push_back( nc );
      childrenChanged = childrenChanged || nc!=body[i];
    }
    if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
}*/
/*CVC4::Node QuantifierEliminate::normalizeBody(CVC4::Node body)
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
}*/
/*Node QuantifierEliminate::simplifyExpression(Node n)
{
  // 1st phase of simplification is converting the expression to NNF
  Node nnfNode = convertToNNF(n);
  // 3rd phase of simplification is applying the replace rules
  //Node normalizedBody = normalizeBody(nnfNode);
  // 4th phase of simplification is
  return nnfNode;
}*/

