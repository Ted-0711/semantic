// eslint-disable-next-line no-unused-vars
import { err_code } from '../grammatical_analysis/grammar'

let errString_3 = "";

// 标识符类型
const IdType = {
	Function: 0,
	Variable: 1,
	TempVar: 2,
	ConstVar: 3,
	ReturnVar: 4,
};

// 表类型
const TableType = {
	GlobalTable: 0,
	FunctionTable: 1,
	BlockTable: 2,
	TmpTable: 3,
};

// 四元式
class Quat {
	constructor(index = -1, oprType = "", arg1 = "", arg2 = "", result = "") {
		this.index = index;
		this.oprType = oprType;
		this.arg1 = arg1;
		this.arg2 = arg2;
		this.result = result;
	}
}

// 语义分析中的符号
class SemanticSym {
	constructor(token = "", value = "", row = -1, col = -1, tableIndex = -1, index = -1) {
		this.token = token						// token类型
		this.value = value						// 值
		this.row = row								// 行
		this.col = col								// 列
		this.tableIndex = tableIndex	// 符号所在table的index
		this.index = index						// 符号在table内部的index
	}
}

// 标识符信息
class IdInfo {
	constructor(idType = -1, specType = "", idName = "", funcParamNum = -1, funcEntry = -1, funcTableIndex = -1) {
		this.idType = idType;									// 标识符类型
		this.specType = specType;							// 变(常)量类型/函数返回类型
		this.idName = idName;									// 标识符名称/常量值
		this.funcParamNum = funcParamNum;			// 函数参数个数
		this.funcEntry = funcEntry;						// 函数入口地址（四元式标号）
		this.funcTableIndex = funcTableIndex;	// 函数的函数符号表在整个程序的符号表列表中的索引
	}
}

// 语义分析中的符号表
class SemanticSymTable {
	constructor(tableType, tableName) {
		this.tableType = tableType;			// 表的类型
		this.tableName = tableName;		// 表名
		this.table = [];								// 符号表
	}

	// 寻找一个变量
	FindSym(idName) {
		for (let i = 0; i < this.table.length; i++) {
			if (this.table[i].idName == idName)
				return i;		// 找到
		}
		// 未找到
		return -1;
	}

	// 加入一个变量，返回加入的位置
	AddSym(id) {
		if (this.FindSym(id.idName) == -1) {
			// 未找到则加入
			this.table.push(id);
			return this.table.length - 1;
		}
		// 已存在
		return -1;
	}
}

// 语义分析
class SemanticAnalysis {
	constructor() {
		errString_3 = "";
		this.quat = [];							// 四元式
		this.mainIndex = -1;				// main四元式序号
		this.backpatchLevel = -1;		// 回填层次
		this.backpatchList = [];		// 回填列表
		this.nextQuatIndex = -1;		// 下一个四元式标号
		this.tmpVarCount = -1;			// 临时变量计数
		this.symList = [];					// 语义分析过程的符号流
		this.tables = [];						// 程序所有符号表
		this.curTableStack = [];		// 当前作用于对应的符号表索引栈

		this.tables.push(new SemanticSymTable(TableType.GlobalTable, "global table"));
		this.curTableStack.push(0);
		this.tables.push(new SemanticSymTable(TableType.TmpTable, "tmp variable table"));
		this.nextQuatIndex = 1;
		this.mainIndex = -1;
		this.backpatchLevel = 0;
		this.tmpVarCount = 0;
	}

	// 将所有的符号信息放入symList
	AddSymToList(sym) {
		this.symList.push(sym)
	}

	// 输出四元式表
	GenQuat() {
		let res = [];
		for (let i = 0; i < this.quat.length; i++) {
			res.push({ index: this.quat[i].index, op: this.quat[i].oprType, arg1: this.quat[i].arg1, arg2: this.quat[i].arg2, result: this.quat[i].result });
			// res += this.quat[i].index + "\t(" + this.quat[i].oprType + ", " + this.quat[i].arg1 + ", " + this.quat[i].arg2 + ", " + this.quat[i].result + ")\n";
		}
		return res;
	}

	// 分析过程
	Analysis(prodLeft, prodRight) {
		if (prodLeft == "Program") this.AnlysProd_Program(prodLeft, prodRight);
		else if (prodLeft == "Declare") this.AnlysProd_Declare(prodLeft, prodRight);
		else if (prodLeft == "VarCat") this.AnlysProd_VarCat(prodLeft, prodRight);
		else if (prodLeft == "FunRetCat") this.AnlysProd_FunRetCat(prodLeft, prodRight);
		else if (prodLeft == "FunDec") this.AnlysProd_FunDec(prodLeft, prodRight);
		else if (prodLeft == "CreateFunTable_m") this.AnlysProd_CreateFunTable_m(prodLeft, prodRight);
		else if (prodLeft == "ParamDec") this.AnlysProd_ParamDec(prodLeft, prodRight);
		else if (prodLeft == "Block") this.AnlysProd_Block(prodLeft, prodRight);
		else if (prodLeft == "Def") this.AnlysProd_Def(prodLeft, prodRight);
		else if (prodLeft == "AssignStmt") this.AnlysProd_AssignStmt(prodLeft, prodRight);
		else if (prodLeft == "Exp") this.AnlysProd_Exp(prodLeft, prodRight);
		else if (prodLeft == "AddSubExp") this.AnlysProd_AddSubExp(prodLeft, prodRight);
		else if (prodLeft == "Item") this.AnlysProd_Item(prodLeft, prodRight);
		else if (prodLeft == "Factor") this.AnlysProd_Factor(prodLeft, prodRight);
		else if (prodLeft == "CallStmt") this.AnlysProd_CallStmt(prodLeft, prodRight);
		else if (prodLeft == "CallFunCheck") this.AnlysProd_CallFunCheck(prodLeft, prodRight);
		else if (prodLeft == "Args") this.AnlysProd_Args(prodLeft, prodRight);
		else if (prodLeft == "ReturnStmt") this.AnlysProd_ReturnStmt(prodLeft, prodRight);
		else if (prodLeft == "Relop") this.AnlysProd_Relop(prodLeft, prodRight);
		else if (prodLeft == "IfStmt") this.AnlysProd_IfStmt(prodLeft, prodRight);
		else if (prodLeft == "IfStmt_m1") this.AnlysProd_IfStmt_m1(prodLeft, prodRight);
		else if (prodLeft == "IfStmt_m2") this.AnlysProd_IfStmt_m2(prodLeft, prodRight);
		else if (prodLeft == "IfNext") this.AnlysProd_IfNext(prodLeft, prodRight);
		else if (prodLeft == "IfStmt_next") this.AnlysProd_IfStmt_next(prodLeft, prodRight);
		else if (prodLeft == "WhileStmt") this.AnlysProd_WhileStmt(prodLeft, prodRight);
		else if (prodLeft == "WhileStmt_m1") this.AnlysProd_WhileStmt_m1(prodLeft, prodRight);
		else if (prodLeft == "WhileStmt_m2") this.AnlysProd_WhileStmt_m2(prodLeft, prodRight);
		else {
			if (prodRight[0] != "@") {
				let count = prodRight.length;
				while (count--) this.symList.pop();
			}
			this.symList.push(new SemanticSym(prodLeft, "", -1, -1, -1, -1))
		}
	}

	// Program ::= DeclareList 
	AnlysProd_Program(prodLeft, prodRight) {
		// 如果没有定义main函数，则报错
		if (this.mainIndex == -1) {
			errString_3 += "未定义main函数\n";
			// throw (err_code.SEMANTIC_ERROR_NO_MAIN);
			return;
		}
		let count = prodRight.length;
		while (count--) this.symList.pop();

		this.quat.splice(0, 0, new Quat(0, "j", "_", "_", String(this.mainIndex)));
		this.symList.push(new SemanticSym(prodLeft, "", -1, -1, -1, -1));
	}

	//Declare ::= VarCat <ID> ; | FunRetCat FunDec Block
	AnlysProd_Declare(prodLeft, prodRight) {
		if (prodRight.length == 3) {
			let spec = this.symList[this.symList.length - 3],
				id = this.symList[this.symList.length - 2], curTable = this.tables[this.curTableStack[this.curTableStack.length - 1]];
			if (curTable.FindSym(id.value) != -1) {
				errString_3 += "变量" + id.value + "重定义（" + id.row + "行，" + id.col + "列）\n";
				// throw (err_code.SEMANTIC_ERROR_REDEFINED);
				return;
			}

			let variable = new IdInfo(IdType.Variable, spec.value, id.value);
			this.tables[this.curTableStack[this.curTableStack.length - 1]].AddSym(variable);
			let count = prodRight.length;
			while (count--) {
				this.symList.pop();
			}
			this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, this.curTableStack[this.curTableStack.length - 1], this.tables[this.curTableStack[this.curTableStack.length - 1]].table.length - 1))
		}
		// 函数定义
		else {
			let id = this.symList[this.symList.length - 2];
			this.curTableStack.pop();
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, id.tableIndex, id.index));
		}
	}

	// VarCat ::= int
	AnlysProd_VarCat(prodLeft, prodRight) {
		let spec = this.symList[this.symList.length - 1], count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, spec.value, spec.row, spec.col, -1, -1));
	}

	// FunRetCat ::= void | int 
	AnlysProd_FunRetCat(prodLeft, prodRight) {
		let spec = this.symList[this.symList.length - 1];
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, spec.value, spec.row, spec.col, -1, -1));
	}

	// FunDec ::= <ID> CreateFunTable_m ( VarList )
	AnlysProd_FunDec(prodLeft, prodRight) {
		let spec = this.symList[this.symList.length - 4], count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, spec.value, spec.row, spec.col, spec.tableIndex, spec.index));
	}

	// CreateFunTable_m ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_CreateFunTable_m(prodLeft, prodRight) {
		let id = this.symList[this.symList.length - 1];
		let spec = this.symList[this.symList.length - 2];

		if (this.tables[0].FindSym(id.value) != -1) {
			errString_3 += "函数" + id.value + "重定义（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_REDEFINED);
			return;
		}

		this.tables.push(new SemanticSymTable(TableType.FunctionTable, id.value));
		this.tables[0].AddSym(new IdInfo(IdType.Function, spec.value, id.value, 0, 0, this.tables.length - 1));
		this.curTableStack.push(this.tables.length - 1);
		let return_value = new IdInfo(IdType.ReturnVar, spec.value, this.tables[this.tables.length - 1].tableName + "_return_value");
		if (id.value == "main") this.mainIndex = this.nextQuatIndex;
		this.quat.push(new Quat(this.nextQuatIndex++, id.value, "_", "_", "_"));
		this.tables[this.curTableStack[this.curTableStack.length - 1]].AddSym(return_value);
		this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, 0, this.tables[0].table.length - 1));
	}

	// ParamDec ::= VarCat <ID>
	AnlysProd_ParamDec(prodLeft, prodRight) {
		let id = this.symList[this.symList.length - 1], spec = this.symList[this.symList.length - 2], funcTable = this.tables[this.curTableStack[this.curTableStack.length - 1]];
		if (funcTable.FindSym(id.value) != -1) {
			errString_3 += "函数参数" + id.value + "重定义（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_REDEFINED);
			return;
		}
		let new_position = funcTable.AddSym(new IdInfo(IdType.Variable, spec.value, id.value, -1, -1, -1));
		let table_position = this.tables[0].FindSym(funcTable.tableName);
		console.log("this.tables[0]: ", this.tables[0]);
		console.log("table_position: ", table_position);
		console.log("funcTable: ", funcTable);
		this.tables[0].table[table_position].funcParamNum++;
		this.quat.push(new Quat(this.nextQuatIndex++, "defpar", "_", "_", id.value));
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, this.curTableStack[this.curTableStack.length - 1], new_position));
	}

	//Block ::= { DefList StmtList }
	AnlysProd_Block(prodLeft, prodRight) {
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1));
	}

	//Def ::= VarCat <ID> ;
	AnlysProd_Def(prodLeft, prodRight) {
		let id = this.symList[this.symList.length - 2], spec = this.symList[this.symList.length - 3], curTable = this.tables[this.curTableStack[this.curTableStack.length - 1]];
		if (curTable.FindSym(id.value) != -1) {
			errString_3 += "变量" + id.value + "重定义（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_REDEFINED);
			return;
		}
		curTable.AddSym(new IdInfo(IdType.Variable, spec.value, id.value, -1, -1, -1));
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, this.curTableStack[this.curTableStack.length - 1], this.tables[this.curTableStack[this.curTableStack.length - 1]].table.length - 1));

	}

	//AssignStmt ::= <ID> = Exp
	AnlysProd_AssignStmt(prodLeft, prodRight) {
		let id = this.symList[this.symList.length - 3], exp = this.symList[this.symList.length - 1], existed = false, tableIndex = -1, index = -1;
		for (let scope_layer = this.curTableStack.length - 1; scope_layer >= 0; scope_layer--) {
			let curTable = this.tables[this.curTableStack[scope_layer]];
			if ((index = curTable.FindSym(id.value)) != -1) {
				existed = true;
				tableIndex = this.curTableStack[scope_layer];
				break;
			}
		}
		if (existed == false) {
			errString_3 += "变量" + id.value + "未定义（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_UNDEFINED);
			return;
		}
		this.quat.push(new Quat(this.nextQuatIndex++, "=", exp.value, "_", id.value));
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, id.value, id.row, id.col, tableIndex, index));
	}

	//Exp ::= AddSubExp | Exp Relop AddSubExp
	AnlysProd_Exp(prodLeft, prodRight) {
		if (prodRight.length == 1) {
			let exp = this.symList[this.symList.length - 1];
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, exp.value, exp.row, exp.col, exp.tableIndex, exp.index));
		}
		else {
			let sub_exp1 = this.symList[this.symList.length - 3], op = this.symList[this.symList.length - 2], sub_exp2 = this.symList[this.symList.length - 1], next_labelNum = this.nextQuatIndex++, newTmpVar = "T" + String(this.tmpVarCount++);
			this.quat.push(new Quat(next_labelNum, "j" + op.value, sub_exp1.value, sub_exp2.value, String(next_labelNum + 3)));
			this.quat.push(new Quat(this.nextQuatIndex++, "=", "0", "_", newTmpVar));
			this.quat.push(new Quat(this.nextQuatIndex++, "j", "_", "_", String(next_labelNum + 4)));
			this.quat.push(new Quat(this.nextQuatIndex++, "=", "1", "_", newTmpVar));

			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, newTmpVar, -1, -1, -1, -1))
		}
	}

	// AddSubExp ::= Item | Item + Item | Item - Item
	AnlysProd_AddSubExp(prodLeft, prodRight) {
		if (prodRight.length == 1) {
			let exp = this.symList[this.symList.length - 1];
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, exp.value, exp.row, exp.col, exp.tableIndex, exp.index));
		}
		else {
			let sub_exp1 = this.symList[this.symList.length - 3], op = this.symList[this.symList.length - 2], sub_exp2 = this.symList[this.symList.length - 1], newTmpVar = "T" + String(this.tmpVarCount++);
			this.quat.push(new Quat(this.nextQuatIndex++, op.value, sub_exp1.value, sub_exp2.value, newTmpVar));
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, newTmpVar, -1, -1, -1, -1));
		}
	}

	//Item ::= Factor | Factor * Factor | Factor / Factor
	AnlysProd_Item(prodLeft, prodRight) {
		if (prodRight.length == 1) {
			let exp = this.symList[this.symList.length - 1];
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, exp.value, exp.row, exp.col, exp.tableIndex, exp.index));
		}
		else {
			let sub_exp1 = this.symList[this.symList.length - 3];
			let op = this.symList[this.symList.length - 2];
			let sub_exp2 = this.symList[this.symList.length - 1];
			let newTmpVar = "T" + String(this.tmpVarCount++);
			this.quat.push(new Quat(this.nextQuatIndex++, op.value, sub_exp1.value, sub_exp2.value, newTmpVar));

			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, newTmpVar, -1, -1, -1, -1));
		}
	}

	// Factor ::= <INT> | ( Exp ) | <ID> | CallStmt
	AnlysProd_Factor(prodLeft, prodRight) {
		if (prodRight.length == 1) {
			let exp = this.symList[this.symList.length - 1];
			if (prodRight[0] == "<ID>") {
				let existed = false;
				for (let scope_layer = this.curTableStack.length - 1; scope_layer >= 0; scope_layer--) {
					let curTable = this.tables[this.curTableStack[scope_layer]];
					if (curTable.FindSym(exp.value) != -1) {
						existed = true;
						break;
					}
				}
				if (existed == false) {
					errString_3 += "变量" + exp.value + "未定义（" + exp.row + "行，" + exp.col + "列）\n";
					// throw (err_code.SEMANTIC_ERROR_UNDEFINED);
					return;
				}
			}
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, exp.value, exp.row, exp.col, exp.tableIndex, exp.index));
		}
		else {
			let exp = this.symList[this.symList.length - 2], count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, exp.value, exp.row, exp.col, exp.tableIndex, exp.index));
		}
	}

	// CallStmt ::= <ID> ( CallFunCheck Args )
	AnlysProd_CallStmt(prodLeft, prodRight) {
		let id = this.symList[this.symList.length - 5], check = this.symList[this.symList.length - 3], args = this.symList[this.symList.length - 2];

		if (typeof (this.tables[check.tableIndex]) == "undefined") {
			return;
		}
		let paraNum = this.tables[check.tableIndex].table[check.index].funcParamNum;
		if (paraNum > Number(args.value)) {
			errString_3 += "函数" + id.value + "调用时参数过少（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_PARAMETER_NUM);
			return;
		}
		else if (paraNum < Number(args.value)) {
			errString_3 += "函数" + id.value + "调用时参数过多（" + id.row + "行，" + id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_PARAMETER_NUM);
			return;
		}
		let newTmpVar = "T" + String(this.tmpVarCount++);
		this.quat.push(new Quat(this.nextQuatIndex++, "call", id.value, "_", newTmpVar));
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, newTmpVar, -1, -1, -1, -1));
	}

	// CallFunCheck ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_CallFunCheck(prodLeft, prodRight) {
		let fun_id = this.symList[this.symList.length - 2], fun_id_pos = this.tables[0].FindSym(fun_id.value);
		if (fun_id_pos == -1 || this.tables[0].table[fun_id_pos].idType != IdType.Function) {
			errString_3 += "函数" + fun_id.value + "调用未定义（" + fun_id.row + "行，" + fun_id.col + "列）\n";
			// throw (err_code.SEMANTIC_ERROR_UNDEFINED);
			return;
		}

		this.symList.push(new SemanticSym(prodLeft, fun_id.value, fun_id.row, fun_id.col, 0, fun_id_pos));
	}

	// Args ::= Exp , Args | Exp | @
	AnlysProd_Args(prodLeft, prodRight) {
		if (prodRight.length == 3) {
			let exp = this.symList[this.symList.length - 3];
			this.quat.push(new Quat(this.nextQuatIndex++, "param", exp.value, "_", "_"));
			let aruNum = Number(this.symList[this.symList.length - 1].value) + 1;
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, String(aruNum), -1, -1, -1, -1));
		}
		else if (prodRight[0] == "Exp") {
			let exp = this.symList[this.symList.length - 1];
			this.quat.push(new Quat(this.nextQuatIndex++, "param", exp.value, "_", "_"));
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, "1", -1, -1, -1, -1));
		}
		else if (prodRight[0] == "@") {
			this.symList.push(new SemanticSym(prodLeft, "0", -1, -1, -1, -1));
		}
	}

	// ReturnStmt ::= return Exp | return
	AnlysProd_ReturnStmt(prodLeft, prodRight) {
		if (prodRight.length == 2) {
			let return_exp = this.symList[this.symList.length - 1], funcTable = this.tables[this.curTableStack[this.curTableStack.length - 1]];
			this.quat.push(new Quat(this.nextQuatIndex++, "=", return_exp.value, "_", funcTable.table[0].idName));
			this.quat.push(new Quat(this.nextQuatIndex++, "return", funcTable.table[0].idName, "_", funcTable.tableName));
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, return_exp.value, -1, -1, -1, -1));
		}
		else {
			// 函数表
			let funcTable = this.tables[this.curTableStack[this.curTableStack.length - 1]];
			console.log("this.tables[0].FindSym(funcTable.tableName): ", this.tables[0].FindSym(funcTable.tableName));
			console.log("this.tables: ", this.tables);
			if (this.tables[0].table[this.tables[0].FindSym(funcTable.tableName)].specType != "void") {
				errString_3 += "函数" + funcTable.tableName + "必须有返回值（" + this.symList[this.symList.length - 1].row + "行，" + (this.symList[this.symList.length - 1].col + "return".length) + "列）\n";
				// throw (err_code.SEMANTIC_ERROR_NO_RETURN);
				return;
			}
			this.quat.push(new Quat(this.nextQuatIndex++, "return", "_", "_", funcTable.tableName));
			let count = prodRight.length;
			while (count--) this.symList.pop();
			this.symList.push(new SemanticSym(prodLeft, "", -1, -1, -1, -1));
		}
	}

	// Relop ::= > | < | >= | <= | == | !=
	AnlysProd_Relop(prodLeft, prodRight) {
		let op = this.symList[this.symList.length - 1], count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, op.value, -1, -1, -1, -1));
	}

	// IfStmt ::= if IfStmt_m1 ( Exp ) IfStmt_m2 Block IfNext
	AnlysProd_IfStmt(prodLeft, prodRight) {
		let ifstmt_m2 = this.symList[this.symList.length - 3];
		let ifnext = this.symList[this.symList.length - 1];
		if (ifnext.value.length == 0) {
			// 真出口
			this.quat[this.backpatchList[this.backpatchList.length - 1]].result = ifstmt_m2.value;
			this.backpatchList.pop();
			// 假出口
			this.quat[this.backpatchList[this.backpatchList.length - 1]].result = String(this.nextQuatIndex);
			this.backpatchList.pop();
		}
		else {
			// if块出口
			this.quat[this.backpatchList[this.backpatchList.length - 1]].result = String(this.nextQuatIndex);
			this.backpatchList.pop();
			// if真出口
			this.quat[this.backpatchList[this.backpatchList.length - 1]].result = ifstmt_m2.value;
			this.backpatchList.pop();
			// if假出口
			this.quat[this.backpatchList[this.backpatchList.length - 1]].result = ifnext.value;
			this.backpatchList.pop();
		}
		this.backpatchLevel--;
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, "", -1, -1, -1, -1));
	}

	// IfStmt_m1 ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_IfStmt_m1(prodLeft, prodRight) {
		this.backpatchLevel++;
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1))
	}

	// IfStmt_m2 ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_IfStmt_m2(prodLeft, prodRight) {
		let if_exp = this.symList[this.symList.length - 2];
		// 待回填四元式 假出口
		this.quat.push(new Quat(this.nextQuatIndex++, "j=", if_exp.value, "0", ""));
		this.backpatchList.push(this.quat.length - 1);
		// 待回填四元式 真出口
		this.quat.push(new Quat(this.nextQuatIndex++, "j=", "_", "_", ""));
		this.backpatchList.push(this.quat.length - 1);
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1));
	}

	// IfNext ::= IfStmt_next else Block
	AnlysProd_IfNext(prodLeft, prodRight) {
		let if_stmt_next = this.symList[this.symList.length - 3], count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, if_stmt_next.value, -1, -1, -1, -1));
	}

	// IfStmt_next ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_IfStmt_next(prodLeft, prodRight) {
		// if的跳出语句（else之前）（待回填）
		this.quat.push(new Quat(this.nextQuatIndex++, "j", "_", "_", ""));
		this.backpatchList.push(this.quat.length - 1);
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1));
	}

	// WhileStmt ::= while WhileStmt_m1 ( Exp ) WhileStmt_m2 Block
	AnlysProd_WhileStmt(prodLeft, prodRight) {
		let whilestmt_m1 = this.symList[this.symList.length - 6], whilestmt_m2 = this.symList[this.symList.length - 2];
		// 无条件跳转到while的条件判断语句处
		this.quat.push(new Quat(this.nextQuatIndex++, "j", "_", "_", whilestmt_m1.value));
		// 回填真出口
		this.quat[this.backpatchList[this.backpatchList.length - 1]].result = whilestmt_m2.value;
		this.backpatchList.pop();
		// 回填假出口
		this.quat[this.backpatchList[this.backpatchList.length - 1]].result = String(this.nextQuatIndex);
		this.backpatchList.pop();
		this.backpatchLevel--;
		let count = prodRight.length;
		while (count--) this.symList.pop();
		this.symList.push(new SemanticSym(prodLeft, "", -1, -1, -1, -1));
	}

	// WhileStmt_m1 ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_WhileStmt_m1(prodLeft, prodRight) {
		this.backpatchLevel++;
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1));
	}

	// WhileStmt_m2 ::= @
	// eslint-disable-next-line no-unused-vars
	AnlysProd_WhileStmt_m2(prodLeft, prodRight) {
		let while_exp = this.symList[this.symList.length - 2];
		// 假出口
		this.quat.push(new Quat(this.nextQuatIndex++, "j=", while_exp.value, "0", ""));
		this.backpatchList.push(this.quat.length - 1);
		// 真出口
		this.quat.push(new Quat(this.nextQuatIndex++, "j", "_", "_", ""));
		this.backpatchList.push(this.quat.length - 1);
		this.symList.push(new SemanticSym(prodLeft, String(this.nextQuatIndex), -1, -1, -1, -1))
	}
}

export { SemanticSym, SemanticAnalysis, errString_3 }