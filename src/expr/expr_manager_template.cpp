/*********************                                                        */
/*! \file expr_manager_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic, Christopher L. Conway
 ** Minor contributors (to current version): Kshitij Bansal, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression manager interface, implementation
 **
 ** Public-facing expression manager interface, implementation.
 **/

#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "context/context.h"
#include "options/options.h"
#include "util/statistics_registry.h"

#include <map>

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 33 "${template}"

#ifdef CVC4_STATISTICS_ON
  #define INC_STAT(kind) \
  { \
    if (d_exprStatistics[kind] == NULL) { \
      stringstream statName; \
      statName << "expr::ExprManager::" << kind; \
      d_exprStatistics[kind] = new IntStat(statName.str(), 0); \
      d_nodeManager->getStatisticsRegistry()->registerStat_(d_exprStatistics[kind]); \
    } \
    ++ *(d_exprStatistics[kind]); \
  }
  #define INC_STAT_VAR(type, bound_var) \
  { \
    TypeNode* typeNode = Type::getTypeNode(type); \
    TypeConstant type = typeNode->getKind() == kind::TYPE_CONSTANT ? typeNode->getConst<TypeConstant>() : LAST_TYPE; \
    if (d_exprStatisticsVars[type] == NULL) { \
      stringstream statName; \
      if (type == LAST_TYPE) { \
        statName << "expr::ExprManager::" << ((bound_var) ? "BOUND_VARIABLE" : "VARIABLE") << ":Parameterized type"; \
      } else { \
        statName << "expr::ExprManager::" << ((bound_var) ? "BOUND_VARIABLE" : "VARIABLE") << ":" << type; \
      } \
      d_exprStatisticsVars[type] = new IntStat(statName.str(), 0); \
      d_nodeManager->getStatisticsRegistry()->registerStat_(d_exprStatisticsVars[type]); \
    } \
    ++ *(d_exprStatisticsVars[type]); \
  }
#else
  #define INC_STAT(kind)
  #define INC_STAT_VAR(type, bound_var)
#endif

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {

ExprManager::ExprManager() :
  d_ctxt(new Context()),
  d_nodeManager(new NodeManager(d_ctxt, this)) {
#ifdef CVC4_STATISTICS_ON
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    d_exprStatistics[i] = NULL;
  }
  for (unsigned i = 0; i < LAST_TYPE; ++ i) {
    d_exprStatisticsVars[i] = NULL;
  }
#endif
}

ExprManager::ExprManager(const Options& options) :
  d_ctxt(new Context()),
  d_nodeManager(new NodeManager(d_ctxt, this, options)) {
#ifdef CVC4_STATISTICS_ON
  for (unsigned i = 0; i < LAST_TYPE; ++ i) {
    d_exprStatisticsVars[i] = NULL;
  }
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    d_exprStatistics[i] = NULL;
  }
#endif
}

ExprManager::~ExprManager() throw() {
  NodeManagerScope nms(d_nodeManager);

  try {

#ifdef CVC4_STATISTICS_ON
    for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
      if (d_exprStatistics[i] != NULL) {
        d_nodeManager->getStatisticsRegistry()->unregisterStat_(d_exprStatistics[i]);
        delete d_exprStatistics[i];
      }
    }
    for (unsigned i = 0; i < LAST_TYPE; ++ i) {
      if (d_exprStatisticsVars[i] != NULL) {
        d_nodeManager->getStatisticsRegistry()->unregisterStat_(d_exprStatisticsVars[i]);
        delete d_exprStatisticsVars[i];
      }
    }
#endif

    delete d_nodeManager;
    delete d_ctxt;

  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << std::endl
              << e << std::endl;
  }
}

StatisticsRegistry* ExprManager::getStatisticsRegistry() throw() {
  return d_nodeManager->getStatisticsRegistry();
}

const Options& ExprManager::getOptions() const {
  return d_nodeManager->getOptions();
}

BooleanType ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  return BooleanType(Type(d_nodeManager, new TypeNode(d_nodeManager->booleanType())));
}

StringType ExprManager::stringType() const {
  NodeManagerScope nms(d_nodeManager);
  return StringType(Type(d_nodeManager, new TypeNode(d_nodeManager->stringType())));
}

RealType ExprManager::realType() const {
  NodeManagerScope nms(d_nodeManager);
  return RealType(Type(d_nodeManager, new TypeNode(d_nodeManager->realType())));
}

IntegerType ExprManager::integerType() const {
  NodeManagerScope nms(d_nodeManager);
  return IntegerType(Type(d_nodeManager, new TypeNode(d_nodeManager->integerType())));
}

Expr ExprManager::mkExpr(Kind kind, Expr child1) {
  const unsigned n = 1 - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2) {
  const unsigned n = 2 - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2,
                         Expr child3) {
  const unsigned n = 3 - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2,
                         Expr child3, Expr child4) {
  const unsigned n = 4 - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2,
                         Expr child3, Expr child4,
                         Expr child5) {
  const unsigned n = 5 - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const std::vector<Expr>& children) {
  const unsigned n = children.size() - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0);
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, const std::vector<Expr>& otherChildren) {
  const unsigned n = otherChildren.size() - (kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED ? 1 : 0) + 1;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  nodes.push_back(child1.getNode());

  vector<Expr>::const_iterator it = otherChildren.begin();
  vector<Expr>::const_iterator it_end = otherChildren.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr) {
  const unsigned n = 0;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1) {
  const unsigned n = 1;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(), child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2) {
  const unsigned n = 2;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3) {
  const unsigned n = 3;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3,
                         Expr child4) {
  const unsigned n = 4;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3,
                         Expr child4, Expr child5) {
  const unsigned n = 5;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, const std::vector<Expr>& children) {
  const unsigned n = children.size();
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  CheckArgument(opExpr.getKind() == kind::BUILTIN || kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
                "This Expr constructor is for parameterized kinds only");
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this,d_nodeManager->mkNodePtr(opExpr.getNode(), nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

bool ExprManager::hasOperator(Kind k) {
  return NodeManager::hasOperator(k);
}

Expr ExprManager::operatorOf(Kind k) {
  NodeManagerScope nms(d_nodeManager);

  return d_nodeManager->operatorOf(k).toExpr();
}

/** Make a function type from domain to range. */
FunctionType ExprManager::mkFunctionType(Type domain, Type range) {
  NodeManagerScope nms(d_nodeManager);
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(*domain.d_typeNode, *range.d_typeNode))));
}

/** Make a function type with input types from argTypes. */
FunctionType ExprManager::mkFunctionType(const std::vector<Type>& argTypes, Type range) {
  NodeManagerScope nms(d_nodeManager);
  Assert( argTypes.size() >= 1 );
  std::vector<TypeNode> argTypeNodes;
  for (unsigned i = 0, i_end = argTypes.size(); i < i_end; ++ i) {
    argTypeNodes.push_back(*argTypes[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(argTypeNodes, *range.d_typeNode))));
}

FunctionType ExprManager::mkFunctionType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert( sorts.size() >= 2 );
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(sortNodes))));
}

FunctionType ExprManager::mkPredicateType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert( sorts.size() >= 1 );
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkPredicateType(sortNodes))));
}

TupleType ExprManager::mkTupleType(const std::vector<Type>& types) {
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0, i_end = types.size(); i < i_end; ++ i) {
     typeNodes.push_back(*types[i].d_typeNode);
  }
  return TupleType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkTupleType(typeNodes))));
}

RecordType ExprManager::mkRecordType(const Record& rec) {
  NodeManagerScope nms(d_nodeManager);
  return RecordType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkRecordType(rec))));
}

SExprType ExprManager::mkSExprType(const std::vector<Type>& types) {
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0, i_end = types.size(); i < i_end; ++ i) {
     typeNodes.push_back(*types[i].d_typeNode);
  }
  return SExprType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSExprType(typeNodes))));
}

BitVectorType ExprManager::mkBitVectorType(unsigned size) const {
  NodeManagerScope nms(d_nodeManager);
  return BitVectorType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkBitVectorType(size))));
}

ArrayType ExprManager::mkArrayType(Type indexType, Type constituentType) const {
  NodeManagerScope nms(d_nodeManager);
  return ArrayType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkArrayType(*indexType.d_typeNode, *constituentType.d_typeNode))));
}

DatatypeType ExprManager::mkDatatypeType(const Datatype& datatype) {
  // Not worth a special implementation; this doesn't need to be fast
  // code anyway..
  vector<Datatype> datatypes;
  datatypes.push_back(datatype);
  vector<DatatypeType> result = mkMutualDatatypeTypes(datatypes);
  Assert(result.size() == 1);
  return result.front();
}

std::vector<DatatypeType>
ExprManager::mkMutualDatatypeTypes(const std::vector<Datatype>& datatypes) {
  return mkMutualDatatypeTypes(datatypes, set<Type>());
}

std::vector<DatatypeType>
ExprManager::mkMutualDatatypeTypes(const std::vector<Datatype>& datatypes,
                                   const std::set<Type>& unresolvedTypes) {
  NodeManagerScope nms(d_nodeManager);
  std::map<std::string, DatatypeType> nameResolutions;
  std::vector<DatatypeType> dtts;

  // First do some sanity checks, set up the final Type to be used for
  // each datatype, and set up the "named resolutions" used to handle
  // simple self- and mutual-recursion, for example in the definition
  // "nat = succ(pred:nat) | zero", a named resolution can handle the
  // pred selector.
  for(std::vector<Datatype>::const_iterator i = datatypes.begin(),
        i_end = datatypes.end();
      i != i_end;
      ++i) {
    TypeNode* typeNode;
    if( (*i).getNumParameters() == 0 ) {
      typeNode = new TypeNode(d_nodeManager->mkTypeConst(*i));
    } else {
      TypeNode cons = d_nodeManager->mkTypeConst(*i);
      std::vector< TypeNode > params;
      params.push_back( cons );
      for( unsigned int ip = 0; ip < (*i).getNumParameters(); ++ip ) {
        params.push_back( TypeNode::fromType( (*i).getParameter( ip ) ) );
      }

      typeNode = new TypeNode(d_nodeManager->mkTypeNode(kind::PARAMETRIC_DATATYPE, params));
    }
    Type type(d_nodeManager, typeNode);
    DatatypeType dtt(type);
    CheckArgument(nameResolutions.find((*i).getName()) == nameResolutions.end(),
                  datatypes,
                  "cannot construct two datatypes at the same time "
                  "with the same name `%s'",
                  (*i).getName().c_str());
    nameResolutions.insert(std::make_pair((*i).getName(), dtt));
    dtts.push_back(dtt);
  }

  // Second, set up the type substitution map for complex type
  // resolution (e.g. if "list" is the type we're defining, and it has
  // a selector of type "ARRAY INT OF list", this can't be taken care
  // of using the named resolutions that we set up above.  A
  // preliminary array type was set up, and now needs to have "list"
  // substituted in it for the correct type.
  //
  // @TODO get rid of named resolutions altogether and handle
  // everything with these resolutions?
  std::vector< SortConstructorType > paramTypes;
  std::vector< DatatypeType > paramReplacements;
  std::vector<Type> placeholders;// to hold the "unresolved placeholders"
  std::vector<Type> replacements;// to hold our final, resolved types
  for(std::set<Type>::const_iterator i = unresolvedTypes.begin(),
        i_end = unresolvedTypes.end();
      i != i_end;
      ++i) {
    std::string name;
    if( (*i).isSort() ) {
      name = SortType(*i).getName();
    } else {
      Assert( (*i).isSortConstructor() );
      name = SortConstructorType(*i).getName();
    }
    std::map<std::string, DatatypeType>::const_iterator resolver =
      nameResolutions.find(name);
    CheckArgument(resolver != nameResolutions.end(),
                  unresolvedTypes,
                  "cannot resolve type `%s'; it's not among "
                  "the datatypes being defined", name.c_str());
    // We will instruct the Datatype to substitute "*i" (the
    // unresolved SortType used as a placeholder in complex types)
    // with "(*resolver).second" (the DatatypeType we created in the
    // first step, above).
    if( (*i).isSort() ) {
      placeholders.push_back(*i);
      replacements.push_back( (*resolver).second );
    } else {
      Assert( (*i).isSortConstructor() );
      paramTypes.push_back( SortConstructorType(*i) );
      paramReplacements.push_back( (*resolver).second );
    }
  }

  // Lastly, perform the final resolutions and checks.
  for(std::vector<DatatypeType>::iterator i = dtts.begin(),
        i_end = dtts.end();
      i != i_end;
      ++i) {
    const Datatype& dt = (*i).getDatatype();
    if(!dt.isResolved()) {
      const_cast<Datatype&>(dt).resolve(this, nameResolutions,
                                        placeholders, replacements,
                                        paramTypes, paramReplacements);
    }

    // Now run some checks, including a check to make sure that no
    // selector is function-valued.
    checkResolvedDatatype(*i);
  }

  for(std::vector<NodeManagerListener*>::iterator i = d_nodeManager->d_listeners.begin(); i != d_nodeManager->d_listeners.end(); ++i) {
    (*i)->nmNotifyNewDatatypes(dtts);
  }

  return dtts;
}

void ExprManager::checkResolvedDatatype(DatatypeType dtt) const {
  const Datatype& dt = dtt.getDatatype();

  AssertArgument(dt.isResolved(), dtt, "datatype should have been resolved");

  // for all constructors...
  for(Datatype::const_iterator i = dt.begin(), i_end = dt.end();
      i != i_end;
      ++i) {
    const DatatypeConstructor& c = *i;
    Type testerType CVC4_UNUSED = c.getTester().getType();
    Assert(c.isResolved() &&
           testerType.isTester() &&
           TesterType(testerType).getDomain() == dtt &&
           TesterType(testerType).getRangeType() == booleanType(),
           "malformed tester in datatype post-resolution");
    Type ctorType CVC4_UNUSED = c.getConstructor().getType();
    Assert(ctorType.isConstructor() &&
           ConstructorType(ctorType).getArity() == c.getNumArgs() &&
           ConstructorType(ctorType).getRangeType() == dtt,
           "malformed constructor in datatype post-resolution");
    // for all selectors...
    for(DatatypeConstructor::const_iterator j = c.begin(), j_end = c.end();
        j != j_end;
        ++j) {
      const DatatypeConstructorArg& a = *j;
      Type selectorType = a.getSelector().getType();
      Assert(a.isResolved() &&
             selectorType.isSelector() &&
             SelectorType(selectorType).getDomain() == dtt,
             "malformed selector in datatype post-resolution");
      // This next one's a "hard" check, performed in non-debug builds
      // as well; the other ones should all be guaranteed by the
      // CVC4::Datatype class, but this actually needs to be checked.
      AlwaysAssert(!SelectorType(selectorType).getRangeType().d_typeNode->isFunctionLike(),
                   "cannot put function-like things in datatypes");
    }
  }
}

ConstructorType ExprManager::mkConstructorType(const DatatypeConstructor& constructor, Type range) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkConstructorType(constructor, *range.d_typeNode)));
}

SelectorType ExprManager::mkSelectorType(Type domain, Type range) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkSelectorType(*domain.d_typeNode, *range.d_typeNode)));
}

TesterType ExprManager::mkTesterType(Type domain) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkTesterType(*domain.d_typeNode)));
}

SortType ExprManager::mkSort(const std::string& name, uint32_t flags) const {
  NodeManagerScope nms(d_nodeManager);
  return SortType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSort(name, flags))));
}

SortConstructorType ExprManager::mkSortConstructor(const std::string& name,
                                                   size_t arity) const {
  NodeManagerScope nms(d_nodeManager);
  return SortConstructorType(Type(d_nodeManager,
              new TypeNode(d_nodeManager->mkSortConstructor(name, arity))));
}

/* - not in release 1.0
Type ExprManager::mkPredicateSubtype(Expr lambda)
  throw(TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  try {
    return PredicateSubtype(Type(d_nodeManager,
                new TypeNode(d_nodeManager->mkPredicateSubtype(lambda))));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}
*/

/* - not in release 1.0
Type ExprManager::mkPredicateSubtype(Expr lambda, Expr witness)
  throw(TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  try {
    return PredicateSubtype(Type(d_nodeManager,
                new TypeNode(d_nodeManager->mkPredicateSubtype(lambda, witness))));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}
*/

Type ExprManager::mkSubrangeType(const SubrangeBounds& bounds)
  throw(TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  try {
    return SubrangeType(Type(d_nodeManager,
                new TypeNode(d_nodeManager->mkSubrangeType(bounds))));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

/**
 * Get the type for the given Expr and optionally do type checking.
 *
 * Initial type computation will be near-constant time if
 * type checking is not requested. Results are memoized, so that
 * subsequent calls to getType() without type checking will be
 * constant time.
 *
 * Initial type checking is linear in the size of the expression.
 * Again, the results are memoized, so that subsequent calls to
 * getType(), with or without type checking, will be constant
 * time.
 *
 * NOTE: A TypeCheckingException can be thrown even when type
 * checking is not requested. getType() will always return a
 * valid and correct type and, thus, an exception will be thrown
 * when no valid or correct type can be computed (e.g., if the
 * arguments to a bit-vector operation aren't bit-vectors). When
 * type checking is not requested, getType() will do the minimum
 * amount of checking required to return a valid result.
 *
 * @param e the Expr for which we want a type
 * @param check whether we should check the type as we compute it
 * (default: false)
 */
Type ExprManager::getType(Expr e, bool check) throw (TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  Type t;
  try {
    t = Type(d_nodeManager,
             new TypeNode(d_nodeManager->getType(e.getNode(), check)));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
  return t;
}

Expr ExprManager::mkVar(const std::string& name, Type type, uint32_t flags) {
  Assert(NodeManager::currentNM() == NULL, "ExprManager::mkVar() should only be called externally, not from within CVC4 code.  Please use mkSkolem().");
  NodeManagerScope nms(d_nodeManager);
  Node* n = d_nodeManager->mkVarPtr(name, *type.d_typeNode, flags);
  Debug("nm") << "set " << name << " on " << *n << std::endl;
  INC_STAT_VAR(type, false);
  return Expr(this, n);
}

Expr ExprManager::mkVar(Type type, uint32_t flags) {
  Assert(NodeManager::currentNM() == NULL, "ExprManager::mkVar() should only be called externally, not from within CVC4 code.  Please use mkSkolem().");
  NodeManagerScope nms(d_nodeManager);
  INC_STAT_VAR(type, false);
  return Expr(this, d_nodeManager->mkVarPtr(*type.d_typeNode, flags));
}

Expr ExprManager::mkBoundVar(const std::string& name, Type type) {
  NodeManagerScope nms(d_nodeManager);
  Node* n = d_nodeManager->mkBoundVarPtr(name, *type.d_typeNode);
  Debug("nm") << "set " << name << " on " << *n << std::endl;
  INC_STAT_VAR(type, true);
  return Expr(this, n);
}

Expr ExprManager::mkBoundVar(Type type) {
  NodeManagerScope nms(d_nodeManager);
  INC_STAT_VAR(type, true);
  return Expr(this, d_nodeManager->mkBoundVarPtr(*type.d_typeNode));
}

Expr ExprManager::mkAssociative(Kind kind,
                                const std::vector<Expr>& children) {
  CheckArgument( kind::isAssociative(kind), kind,
                 "Illegal kind in mkAssociative: %s",
                 kind::kindToString(kind).c_str());

  NodeManagerScope nms(d_nodeManager);
  const unsigned int max = maxArity(kind);
  const unsigned int min = minArity(kind);
  unsigned int numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if( numChildren <= max ) {
    return mkExpr(kind,children);
  }

  std::vector<Expr>::const_iterator it = children.begin() ;
  std::vector<Expr>::const_iterator end = children.end() ;

  /* The new top-level children and the children of each sub node */
  std::vector<Node> newChildren;
  std::vector<Node> subChildren;

  while( it != end && numChildren > max ) {
    /* Grab the next max children and make a node for them. */
    for( std::vector<Expr>::const_iterator next = it + max;
         it != next;
         ++it, --numChildren ) {
      subChildren.push_back(it->getNode());
    }
    Node subNode = d_nodeManager->mkNode(kind,subChildren);
    newChildren.push_back(subNode);

    subChildren.clear();
  }

  /* If there's children left, "top off" the Expr. */
  if(numChildren > 0) {
    /* If the leftovers are too few, just copy them into newChildren;
     * otherwise make a new sub-node  */
    if(numChildren < min) {
      for(; it != end; ++it) {
        newChildren.push_back(it->getNode());
      }
    } else {
      for(; it != end; ++it) {
        subChildren.push_back(it->getNode());
      }
      Node subNode = d_nodeManager->mkNode(kind, subChildren);
      newChildren.push_back(subNode);
    }
  }

  /* It's inconceivable we could have enough children for this to fail
   * (more than 2^32, in most cases?). */
  AlwaysAssert( newChildren.size() <= max,
                "Too many new children in mkAssociative" );

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  AlwaysAssert( newChildren.size() >= min,
                "Too few new children in mkAssociative" );

  return Expr(this, d_nodeManager->mkNodePtr(kind,newChildren) );
}

unsigned ExprManager::minArity(Kind kind) {
  return metakind::getLowerBoundForKind(kind);
}

unsigned ExprManager::maxArity(Kind kind) {
  return metakind::getUpperBoundForKind(kind);
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}

Context* ExprManager::getContext() const {
  return d_ctxt;
}

Statistics ExprManager::getStatistics() const throw() {
  return Statistics(*d_nodeManager->getStatisticsRegistry());
}

SExpr ExprManager::getStatistic(const std::string& name) const throw() {
  return d_nodeManager->getStatisticsRegistry()->getStatistic(name);
}

namespace expr {

Node exportInternal(TNode n, ExprManager* from, ExprManager* to, ExprManagerMapCollection& vmap);

TypeNode exportTypeInternal(TypeNode n, NodeManager* from, NodeManager* to, ExprManagerMapCollection& vmap) {
  Debug("export") << "type: " << n << std::endl;
  if(theory::kindToTheoryId(n.getKind()) == theory::THEORY_DATATYPES) {
    throw ExportUnsupportedException
      ("export of types belonging to theory of DATATYPES kinds unsupported");
  }
  if(n.getMetaKind() == kind::metakind::PARAMETERIZED &&
     n.getKind() != kind::SORT_TYPE) {
    throw ExportUnsupportedException
      ("export of PARAMETERIZED-kinded types (other than SORT_KIND) not supported");
  }
  if(n.getKind() == kind::TYPE_CONSTANT) {
    return to->mkTypeConst(n.getConst<TypeConstant>());
  } else if(n.getKind() == kind::BITVECTOR_TYPE) {
    return to->mkBitVectorType(n.getConst<BitVectorSize>());
  } else if(n.getKind() == kind::SUBRANGE_TYPE) {
    return to->mkSubrangeType(n.getSubrangeBounds());
  }
  Type from_t = from->toType(n);
  Type& to_t = vmap.d_typeMap[from_t];
  if(! to_t.isNull()) {
    Debug("export") << "+ mapped `" << from_t << "' to `" << to_t << "'" << std::endl;
    return *Type::getTypeNode(to_t);
  }
  NodeBuilder<> children(to, n.getKind());
  if(n.getKind() == kind::SORT_TYPE) {
    Debug("export") << "type: operator: " << n.getOperator() << std::endl;
    // make a new sort tag in target node manager
    Node sortTag = NodeBuilder<0>(to, kind::SORT_TAG);
    children << sortTag;
  }
  for(TypeNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
    Debug("export") << "type: child: " << *i << std::endl;
    children << exportTypeInternal(*i, from, to, vmap);
  }
  TypeNode out = children.constructTypeNode();// FIXME thread safety
  to_t = to->toType(out);
  return out;
}/* exportTypeInternal() */

}/* CVC4::expr namespace */

Type ExprManager::exportType(const Type& t, ExprManager* em, ExprManagerMapCollection& vmap) {
  Assert(t.d_nodeManager != em->d_nodeManager,
         "Can't export a Type to the same ExprManager");
  NodeManagerScope ems(t.d_nodeManager);
  return Type(em->d_nodeManager,
              new TypeNode(expr::exportTypeInternal(*t.d_typeNode, t.d_nodeManager, em->d_nodeManager, vmap)));
}

${mkConst_implementations}

}/* CVC4 namespace */
