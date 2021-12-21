import { SymType, err_code, Grammar } from './grammar'
import { SemanticSym, SemanticAnalysis, errString_3 } from '../semantic_analysis/semantic_analysis'

let errString_2 = "";

// 分析过程中的动作
const Action = {
	ShiftIn: 0,	// 移入
	Reduce: 1,	// 归约
	Accept: 2,	// 接受
	Error: 3,	// 错误
}

// 具体的动作信息
class ActionInfo {
	constructor(action, info) {
		this.action = action
		this.info = info
	}
}

// function times(str, num) {
// 	if (num <= 0)
// 		return "";
// 	return num > 1 ? str += times(str, --num) : str;
// }

// 一个LR1的项
class LR1Item {
	constructor(leftSym, rightSym, index, dotPos, lookAHDSym) {
		this.leftSym = leftSym;
		this.rightSym = rightSym;
		this.index = index;
		this.dotPos = dotPos;
		this.lookAHDSym = lookAHDSym;
	}
	equal(anoLR1Item) {
		return this.leftSym == anoLR1Item.leftSym &&
			this.rightSym == anoLR1Item.rightSym &&
			this.index == anoLR1Item.index &&
			this.dotPos == anoLR1Item.dotPos &&
			this.lookAHDSym == anoLR1Item.lookAHDSym;
	}
}

class LR1Closure {
	constructor() {
		this.lr1Closure = [];
	}
	equal(anoLR1Closure) {
		if (this.lr1Closure.length != anoLR1Closure.lr1Closure.length) return false;
		let count = 0;
		for (let i = 0; i < this.lr1Closure.length; ++i) {
			for (let j = 0; j < anoLR1Closure.lr1Closure.length; ++j) {
				if (this.lr1Closure[i].equal(anoLR1Closure.lr1Closure[j])) {
					++count;
					break;
				}
			}
		}
		return count == this.lr1Closure.length;
	}
}

// LR1文法
class LR1 extends Grammar {
	constructor(grammarFileContent) {
		super(grammarFileContent);
		if (grammarFileContent.length == 0) {
			return;
		}
		// 整个项集族
		this.lr1Cluster = [];
		// goto信息记录表，映射关系为：{当前closure在lr1Cluster中的标号，当前符号在syms中标号} -> 转移到的closure在lr1Cluster中的标号
		this.gotoInfo = new Map();
		// GOTO表，GOTO[i,A]=j，只用到Action Error(表示未定义)和ShiftIn(表示转移)
		this.gotoTable = new Map();
		//ACTION表，ACTION[i, A] = "移入/规约/接受"
		this.actionTable = new Map();
		// 语义分析器
		this.semanticAnalysis = new SemanticAnalysis();
		// 语法树节点列表
		this.nodeList = [];
		// 生成LR1项集，存储在lr1Closure中
		this.genCluster();
		// 生成Table
		this.genTable();
	}
	// 生成LR1项集
	genCluster() {
		// 初始化lr1Cluster({S → ·Program, $})
		let initItem = new LR1Item(this.findSymIndexByToken(this.ExtStartToken), [this.findSymIndexByToken(this.StartToken)], this.startProd, 0, this.findSymIndexByToken(this.EndToken));
		let initClosure = new LR1Closure();
		initClosure.lr1Closure.push(initItem);

		// 放进cluster中
		this.lr1Cluster.push(this.genClosure(initClosure));

		// 遍历lr1Cluster中的每一项
		for (let i = 0; i < this.lr1Cluster.length; ++i) {
			// 遍历所有文法符号
			for (let s = 0; s < this.syms.length; ++s) {
				// 只有为终结符或非终结符才进行下一步
				if (this.syms[s].type != SymType.NonTrm && this.syms[s].type != SymType.Trm) continue;
				// 得到输入符号s会到达的closure
				let toClosure = this.genGOTO(this.lr1Cluster[i], s);
				// 如果为空，则continue
				if (toClosure.lr1Closure.length == 0) continue;
				// 如果已经存在，则记录编号
				let existIndex = -1;
				for (let j = 0; j < this.lr1Cluster.length; j++) {
					if (this.lr1Cluster[j].equal(toClosure)) {
						existIndex = j;
						break;
					}
				}
				if (existIndex != -1) this.gotoInfo.set(String(i) + " " + String(s), existIndex);
				else {
					// 不存在，则加入lr1Cluster
					this.lr1Cluster.push(toClosure);
					// 记录转移关系
					this.gotoInfo.set(String(i) + " " + String(s), this.lr1Cluster.length - 1);
				}
			}
		}
	}
	// 生成闭包
	genClosure(initClosure) {
		for (let i = 0; i < initClosure.lr1Closure.length; ++i) {
			let presentLr1Item = initClosure.lr1Closure[i];
			// ·在最后一个位置，则其后继没有非终结符
			if (presentLr1Item.dotPos >= presentLr1Item.rightSym.length) continue;
			// ·后的符号
			let nextSymIndex = presentLr1Item.rightSym[presentLr1Item.dotPos], nextSym = this.syms[nextSymIndex];
			// 如果·后的符号为终结符
			if (nextSym.type == SymType.Trm) continue;
			// 如果·后的符号为ε，则 -> ·ε 直接变为 -> ε·
			if (nextSym.type == SymType.Epsilon) {
				initClosure.lr1Closure.dotPos++;
				continue;
			}
			// 其他情况，·后符号为非终结符
			// 得到first集（A->α·Bβ, a 则求βa的first集）
			let BetaA = presentLr1Item.rightSym.slice(presentLr1Item.dotPos + 1, presentLr1Item.rightSym.length);
			BetaA.push(presentLr1Item.lookAHDSym);
			let BetaAFirstSet = this.getFirstOfString(BetaA);
			// 查找以nextSymIndex开始的prod
			for (let j = 0; j < this.prods.length; ++j) {
				let presentProd = this.prods[j];
				if (presentProd.leftSym != nextSymIndex) continue;
				// 查找到以nextSymIndex开始的prod，开始加入initClosure
				for (let it = 0; it < BetaAFirstSet.length; ++it) {
					let tmp = 0;
					// 如果是ε产生式，则直接加入->ε·项，从而不引出ε转移边
					if (this.syms[presentProd.rightSym[0]].type == SymType.Epsilon) {
						// 确保当前不含这一项再加入
						for (tmp = 0; tmp < initClosure.lr1Closure.length; ++tmp) {
							if (initClosure.lr1Closure[tmp].equal(new LR1Item(presentProd.leftSym, presentProd.rightSym, j, 1, BetaAFirstSet[it]))) break;
						}
						if (tmp == initClosure.lr1Closure.length)
							initClosure.lr1Closure.push(new LR1Item(presentProd.leftSym, presentProd.rightSym, j, 1, BetaAFirstSet[it]));
					}
					else {
						// 确保当前不含这一项再加入
						for (tmp = 0; tmp < initClosure.lr1Closure.length; ++tmp) {
							if (initClosure.lr1Closure[tmp].equal(new LR1Item(presentProd.leftSym, presentProd.rightSym, j, 0, BetaAFirstSet[it]))) break;
						}
						if (tmp == initClosure.lr1Closure.length)
							initClosure.lr1Closure.push(new LR1Item(presentProd.leftSym, presentProd.rightSym, j, 0, BetaAFirstSet[it]));
					}
				}
			}
		}
		return initClosure;
	}
	// 生成GOTO的closure
	genGOTO(fromClosure, presentSym) {
		let toClosure = new LR1Closure();
		// 判断一下presentSym是不是非终结符或终结符（虽然按理来说应该已经判断过了），如果不合要求返回空
		if (this.syms[presentSym].type != SymType.NonTrm && this.syms[presentSym].type != SymType.Trm)
			return toClosure;
		for (let lr1ItemIt = 0; lr1ItemIt < fromClosure.lr1Closure.length; ++lr1ItemIt) {
			// 如果dot在最后
			if (fromClosure.lr1Closure[lr1ItemIt].dotPos >= fromClosure.lr1Closure[lr1ItemIt].rightSym.length)
				continue;
			// 如果后面一个字符不是presentSym
			if (fromClosure.lr1Closure[lr1ItemIt].rightSym[fromClosure.lr1Closure[lr1ItemIt].dotPos] != presentSym)
				continue;
			// 后面一个字符就是presentSym
			toClosure.lr1Closure.push(new LR1Item(fromClosure.lr1Closure[lr1ItemIt].leftSym, fromClosure.lr1Closure[lr1ItemIt].rightSym, fromClosure.lr1Closure[lr1ItemIt].index, fromClosure.lr1Closure[lr1ItemIt].dotPos + 1, fromClosure.lr1Closure[lr1ItemIt].lookAHDSym));
		}
		return this.genClosure(toClosure);
	}
	// 进行语法分析
	parser(tokenStream, idList, constList) {
		errString_2 = "";
		this.semanticAnalysis = new SemanticAnalysis();
		let parseArray = [], tmpArray = [], tmp = 0;
		this.nodeList = [];

		// 在tokenStream的末尾添加EndToken
		tokenStream.push({ type: this.EndToken, prop: this.EndToken, row: -1, col: -1 });
		// 定义符号栈 状态栈  记录步骤 树节点
		let symStack = [], statusStack = [], step = 1, tmpStack = [];

		// 用于输出的格式化
		// let step_len = 5, status_len = 200, sym_len = 300, input_len = 200, prod_len = 60;
		// 输出一行的函数
		let print_line = (i, prodIndex) => {
			// 输出第几步
			tmpArray.push(step++);
			// outString += times(" ", step_len - String(step).length) + String(step++);
			// 状态栈的string
			let statusStackStr = "";
			for (let status = 0; status < statusStack.length; ++status) {
				statusStackStr += " " + String(statusStack[status]);
			}
			tmpArray.push(statusStackStr);
			// outString += times(" ", status_len - statusStackStr.length) + statusStackStr;
			// 符号栈的string
			let symStackStr = "";
			for (let sym = 0; sym < symStack.length; ++sym) {
				symStackStr += "(" + String(symStack[sym]) + "," + this.syms[symStack[sym]].token + ")";
			}
			tmpArray.push(symStackStr);
			// outString += times(" ", sym_len - symStackStr.length) + symStackStr;
			// 输入串的string
			let inputStr = "";
			for (let token = i; token < tokenStream.length; ++token) {
				inputStr += tokenStream[token].type;
			}
			tmpArray.push(inputStr);
			// outString += times(" ", input_len - inputStr.length) + inputStr;
			// 产生式的string
			if (prodIndex != -1) {
				let prodStr = "";
				prodStr += this.syms[this.prods[prodIndex].leftSym].token;
				prodStr += " ::= ";
				for (let prodRightSym = 0; prodRightSym < this.prods[prodIndex].rightSym.length; ++prodRightSym) {
					prodStr += this.syms[this.prods[prodIndex].rightSym[prodRightSym]].token + " ";
				}
				tmpArray.push(prodStr);
				// outString += times(" ", prod_len - prodStr.length) + prodStr;
			}
			parseArray.push(tmpArray);
			tmpArray = [];
			// outString += "\n";
		};

		// 输出
		// outString += times(" ", step_len - 4) + "步骤" + times(" ", status_len - 4) + "状态" + times(" ", sym_len - 4) + "符号" + times(" ", input_len - 4) + "输入串" + times(" ", prod_len - 6) + "产生式" + "\n";

		this.semanticAnalysis.AddSymToList(new SemanticSym(this.StartToken, "", -1, -1, -1, -1));

		// 初始化栈
		symStack.push(this.findSymIndexByToken(this.EndToken));
		statusStack.push(0);

		// 输出
		print_line(0, -1);

		// 对tokenStream中的每一个符号进行遍历
		for (let i = 0; i < tokenStream.length; ++i) {
			let cur_state = statusStack[statusStack.length - 1], curTokenIndex = this.findSymIndexByToken(tokenStream[i].type);
			// 如果找不到这一符号
			if (curTokenIndex == -1) {
				console.log(tokenStream[i]);
				errString_2 = "待分析字符流中出现了未在文法中进行定义的终结符";
				throw (err_code.GRAMMATICAL_ERROR_UNDEFINED_WORD);
			}
			let curActionIter = this.actionTable.get(String(cur_state) + " " + String(curTokenIndex));
			// 如果没有找到，进行报错
			if (curActionIter == undefined) {
				errString_2 = "语法分析过程中在（第" + tokenStream[i].row + "行，第" + tokenStream[i].col + "列）发现错误";
				console.log(errString_2)
				throw (err_code.GRAMMATICAL_ERROR_CANNOT_ANALYSIS)
			}
			// 当前ActionInfo
			let curActioninfo = curActionIter;
			// 根据ActionInfo的类别进行相应的动作
			switch (curActioninfo.action) {
				// 移进
				case Action.ShiftIn: {
					symStack.push(curTokenIndex);
					statusStack.push(curActioninfo.info);
					tmpStack.push(tmp);
					if (tokenStream[i].type == "<ID>") {
						this.nodeList.push({ name: idList[tokenStream[i].prop - 1].value, children: [] })
					}
					else if (tokenStream[i].type == "<INT>" || tokenStream[i].type == "<FLOAT>" || tokenStream[i].type == "<STRING>" || tokenStream[i].type == "<CHAR>") {
						this.nodeList.push({ name: constList[tokenStream[i].prop - 1].value, children: [] })
					}
					else {
						this.nodeList.push({ name: tokenStream[i].type, children: [] })
					}
					++tmp;
					print_line(i + 1, -1);

					if (tokenStream[i].type == "<ID>") {
						this.semanticAnalysis.AddSymToList(new SemanticSym(tokenStream[i].type, idList[tokenStream[i].prop - 1].value, tokenStream[i].row, tokenStream[i].col, -1, -1));
					}
					else if (tokenStream[i].type == "<INT>") {
						this.semanticAnalysis.AddSymToList(new SemanticSym(tokenStream[i].type, constList[tokenStream[i].prop - 1].value, tokenStream[i].row, tokenStream[i].col, -1, -1));
					}
					else {
						this.semanticAnalysis.AddSymToList(new SemanticSym(tokenStream[i].type, tokenStream[i].type, tokenStream[i].row, tokenStream[i].col, -1, -1));
					}
					break;
				}
				// 规约
				case Action.Reduce: {
					// 规约使用的prod
					let prodIndex = curActioninfo.info, prod = this.prods[prodIndex], tmpLeft = [];
					// 非空串需要出栈 空串由于右部为空不需要出栈(直接push空串对应产生式左部非终结符即可)
					if (this.syms[prod.rightSym[0]].type != SymType.Epsilon) {
						let count = prod.rightSym.length;
						while (count--) {
							symStack.pop();
							statusStack.pop();
							tmpLeft.push(tmpStack.pop());
						}
					}
					// 在goto表中寻找
					let curGotoIter = this.gotoTable.get(String(statusStack[statusStack.length - 1]) + " " + String(prod.leftSym));
					// 找不到则报错
					if (curGotoIter == undefined) {
						errString_2 = "语法分析过程中在（第" + tokenStream[i].row + "行，第" + tokenStream[i].col + "列）发现错误";
						throw (err_code.GRAMMATICAL_ERROR_CANNOT_ANALYSIS);
					}
					// 移入符号栈和状态栈
					symStack.push(prod.leftSym);
					statusStack.push(curGotoIter.info);

					tmpStack.push(tmp);
					this.nodeList.push({ name: this.syms[prod.leftSym].token, children: [] });
					++tmp;

					print_line(i, prodIndex);

					if (tmpLeft.length != 0) {
						for (let j = 0; j < tmpLeft.length; ++j) {
							this.nodeList[tmp - 1].children.splice(0, 0, this.nodeList[tmpLeft[j]]);
						}
					}
					else {
						// 空串
						this.nodeList[tmp - 1].children.splice(0, 0, { name: "@" })
					}

					// 此时i不加1
					--i;

					// 进行语义分析
					let prodRight = [];
					for (let s = 0; s < prod.rightSym.length; ++s) {
						prodRight.push(this.syms[prod.rightSym[s]].token);
					}
					this.semanticAnalysis.Analysis(this.syms[prod.leftSym].token, prodRight);
					break;
				}
				// 接受
				case Action.Accept: {
					// 输出acc
					tmpArray.push(step++);
					tmpArray.push("acc!");
					parseArray.push(tmpArray);
					tmpArray = [];
					// outString += times(" ", step_len - String(step).length) + String(step++) + times(" ", status_len - 4) + "acc!\n";
					return parseArray;
				}
				// 错误
				case Action.Error: {
					return parseArray;
				}
			}
		}
	}
	// 打印Table
	genTableArray() {
		let tableArray = [], tmpArray = [], err_msg = " ";

		tmpArray.push("STATUS");

		for (let ter = 0; ter < this.trms.length; ++ter) {
			tmpArray.push(this.syms[this.trms[ter]].token);
		}
		for (let non_ter = 0; non_ter < this.nonTrms.length; ++non_ter) {
			if (this.syms[this.nonTrms[non_ter]].token == this.ExtStartToken) {
				continue;
			}
			tmpArray.push(this.syms[this.nonTrms[non_ter]].token);
		}

		tableArray.push(tmpArray);
		tmpArray = [];

		for (let i = 0; i < this.lr1Cluster.length; ++i) {

			tmpArray.push(i);

			for (let ter = 0; ter < this.trms.length; ++ter) {
				let iter = this.actionTable.get(String(i) + " " + String(this.trms[ter]));
				if (iter == undefined) {
					tmpArray.push(err_msg);
				}
				else {
					let out_msg = "";
					if (iter.action == Action.Accept) {
						out_msg += "acc";
					}
					else if (iter.action == Action.Reduce) {
						out_msg += "r" + String(iter.info);
					}
					else if (iter.action == Action.ShiftIn) {
						out_msg += "s" + String(iter.info)
					}
					tmpArray.push(out_msg);
				}
			}

			for (let non_ter = 0; non_ter < this.nonTrms.length; ++non_ter) {
				if (this.syms[this.nonTrms[non_ter]].token == this.ExtStartToken) {
					continue;
				}
				let iter = this.gotoTable.get(String(i) + " " + String(this.nonTrms[non_ter]));
				if (iter == undefined) {
					tmpArray.push(err_msg);
				}
				else {
					tmpArray.push(iter.info);
				}
			}
			tableArray.push(tmpArray);
			tmpArray = [];
		}
		return tableArray;
	}
	// 生成Table
	genTable() {
		for (let closureIndex = 0; closureIndex < this.lr1Cluster.length; ++closureIndex) {
			for (let lr1ItemIndex = 0; lr1ItemIndex < this.lr1Cluster[closureIndex].lr1Closure.length; ++lr1ItemIndex) {
				let presentLr1Item = this.lr1Cluster[closureIndex].lr1Closure[lr1ItemIndex];
				// 如果·已在末尾
				if (presentLr1Item.dotPos >= presentLr1Item.rightSym.length) {
					// 如果不为扩展开始符号，则进行规约
					console.log("this.syms: ", this.syms);
					console.log("presentLr1Item.leftSym", presentLr1Item.leftSym);
					console.log("this.syms[presentLr1Item.leftSym]", this.syms[presentLr1Item.leftSym]);
					if (this.syms[presentLr1Item.leftSym].token != this.ExtStartToken) {
						// 如果不为扩展开始符号，则进行规约
						this.actionTable.set(String(closureIndex) + " " + String(presentLr1Item.lookAHDSym), new ActionInfo(Action.Reduce, presentLr1Item.index));
					}
					else {
						// 否则为接受
						this.actionTable.set(String(closureIndex) + " " + String(presentLr1Item.lookAHDSym), new ActionInfo(Action.Accept, -1));
					}
				}
				else {
					// 如果·不在末尾
					let nextSym = presentLr1Item.rightSym[presentLr1Item.dotPos];
					// 如果不是终结符，则在goto表中标出
					if (this.syms[nextSym].type == SymType.NonTrm) {
						// 在goto表中寻找
						let it = this.gotoInfo.get(String(closureIndex) + " " + String(nextSym));
						// 如果找到，进行移进
						if (it != undefined) {
							this.gotoTable.set(String(closureIndex) + " " + String(nextSym), new ActionInfo(Action.ShiftIn, it));
						}
					}
					// 否则在action表中标出
					else if (this.syms[nextSym].type == SymType.Trm) {
						// 在goto表中寻找
						let it = this.gotoInfo.get(String(closureIndex) + " " + String(nextSym));
						// 如果找到，进行移进
						if (it != undefined) {
							this.actionTable.set(String(closureIndex) + " " + String(nextSym), new ActionInfo(Action.ShiftIn, it));
						}
					}
				}
			}
		}
	}
}

export { LR1, errString_2, errString_3 }