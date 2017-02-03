///*
// * dummy_esbmc.h
// *
// *  Created on: 2 Feb 2017
// *      Author: esteffin
// */
//
//#ifndef SRC_DUMMY_ESBMC_H_
//#define SRC_DUMMY_ESBMC_H_
//
//#include <string.h>
//#include <memory>
//#include <vector>
//
//class Stmt {
//public:
//	enum StmtType {
//		ASSERT,
//		ASSUME,
//		ASSIGNMENT,
//		OUTPUT
//	};
//	Stmt(StmtType ty) : type(ty) {
//	}
//
//	StmtType type;
//};
//
//class Assignment : public Stmt {
//public:
//	Assignment() {
//		this->type = StmtType::ASSIGNMENT;
//	}
//};
//
//enum ExprType {
//	CONSTANT,
//	VARIABLE,
//	OR_EXPR,
//	AND_EXPR,
//	COND_EXPR
//};
//
//class Expr {
//public:
//	ExprType type;
//};
//
//class Variable : Expr {
//public:
//	Variable(const string name) {
//		type(ExprType::VARIABLE)
//	}
//private:
//	char * name;
//	int id;
//	Expr value;
//};
//
//
//#endif /* SRC_DUMMY_ESBMC_H_ */
