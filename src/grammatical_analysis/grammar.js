let errString = "";

// 文法符号种类
const SymType = {
	Epsilon: 0,
	Trm: 1,
	NonTrm: 2,
	End: 3,
};

// 错误码
const err_code = {
	NO_ERROR: 0,
	FILE_OPEN_ERROE: 1,
	LEXICAL_ERROR_UNDEFINED_WORD: 2,
	GRAMMAR_ERROR: 3,
	GRAMMATICAL_ERROR_UNDEFINED_WORD: 4,
	GRAMMATICAL_ERROR_CANNOT_ANALYSIS: 5,
	// 语义分析相关错误，统一在程序界面展示，不throw(error)
	// SEMANTIC_ERROR_NO_MAIN: 6,
	// SEMANTIC_ERROR_REDEFINED: 7,
	// SEMANTIC_ERROR_UNDEFINED: 8,
	// SEMANTIC_ERROR_PARAMETER_NUM: 9,
	// SEMANTIC_ERROR_NO_RETURN: 10,
};

// 预处理
function split_postproc(arr) {
	for (let i = 0; i < arr.length; i++) {
		arr[i] = arr[i].trim();
	}
	return arr.filter((item) => item != "");
}

// 文法符号
class GrammarSym {
	constructor(type, token) {
		this.type = type;
		this.token = token;
		this.firstSet = [];
		this.followSet = [];
	}
}

// 文法中的项
class GrammarItem {
	constructor(leftSym, rightSym) {
		this.leftSym = leftSym;
		this.rightSym = rightSym;
	}
}

// 整个文法
class Grammar {
	constructor(grammarFileContent) {
		errString = "";

		this.TrmToken = "%token"; 			//终结符
		this.EpsilonToken = "@"; 				// Epsilon
		this.SplitToken = " | "; 				// 右部分隔符
		this.ProToken = "::="; 					// 左右分隔符
		this.EndToken = "#"; 						// 终止符号
		this.StartToken = "Program"; 		// 起始符号
		this.ExtStartToken = "S"; 			// 扩展文法起始符号

		this.syms = []; 								// 所有符号集合
		this.trms = []; 								// 终结符下标
		this.nonTrms = []; 							// 非终结符下标
		this.prods = []; 								// 产生式集合
		this.startProd = 0; 						// 起始产生式在prods中的位置

		if (grammarFileContent.length == 0) {
			return;
		}
		this.readGrammar(grammarFileContent);
		// 初始化终结符first集
		for (let ter = 0; ter < this.trms.length; ++ter) {
			this.syms[this.trms[ter]].firstSet.push(this.trms[ter]);
		}
		// 初始化非终结符first集
		this.getFirstOfNonTrm();
	}
	readGrammar(grammarFileContent) {
		this.syms.push(new GrammarSym(SymType.End, this.EndToken));
		this.trms.push(this.syms.length - 1);
		this.syms.push(
			new GrammarSym(SymType.Epsilon, this.EpsilonToken)
		);

		let pointer = 0, grammarRowNum = 0, line = "";

		while (pointer < grammarFileContent.length) {
			line = "";
			while (
				pointer < grammarFileContent.length &&
				grammarFileContent[pointer] != "\r" &&
				grammarFileContent[pointer] != "\n"
			) {
				line += grammarFileContent[pointer];
				pointer++;
			}
			while (
				pointer < grammarFileContent.length &&
				(grammarFileContent[pointer] == "\r" ||
					grammarFileContent[pointer] == "\n")
			) {
				pointer++;
			}
			grammarRowNum++;
			if (line.indexOf("$") != -1) line = line.slice(0, line.indexOf("$"));
			line = line.trim();
			if (line.length == 0) continue;
			let prodLeftAndRight = line.split(this.ProToken);
			if (prodLeftAndRight.length != 2) {
				errString =
					"第" +
					grammarRowNum +
					'行的产生式格式有误（每行应有且只有一个"' +
					this.ProToken +
					'"符号）';
				throw err_code.GRAMMAR_ERROR;
			}
			let prodLeft = prodLeftAndRight[0].trim(),
				prodRight = prodLeftAndRight[1].trim(), leftSym = -1;
			if (prodLeft != this.TrmToken) {
				leftSym = this.findSymIndexByToken(prodLeft);
				if (leftSym == -1) {
					this.syms.push(
						new GrammarSym(SymType.NonTrm, prodLeft)
					);
					leftSym = this.syms.length - 1;
					this.nonTrms.push(leftSym);
				}
			}
			let prodRightParts = split_postproc(prodRight.split("|"));
			if (prodRightParts.length == 0) {
				errString =
					"第" +
					grammarRowNum +
					"行的产生式格式有误（产生式右端没有文法符号）";
				console.log('t1', errString);
				throw err_code.GRAMMAR_ERROR;
			}
			for (let i = 0; i < prodRightParts.length; i++) {
				if (leftSym == -1) {
					this.syms.push(
						new GrammarSym(SymType.Trm, prodRightParts[i])
					);
					this.trms.push(this.syms.length - 1);
				} else {
					let rightSym = [], rightSymStr = split_postproc(
						prodRightParts[i].split(/\s/)
					);
					for (let j = 0; j < rightSymStr.length; j++) {
						let presentRightSym = this.findSymIndexByToken(
							rightSymStr[j]
						);
						if (presentRightSym == -1) {
							this.syms.push(
								new GrammarSym(SymType.NonTrm, rightSymStr[j])
							);
							presentRightSym = this.syms.length - 1;
							this.nonTrms.push(presentRightSym);
						}
						rightSym.push(presentRightSym);
					}
					this.prods.push(new GrammarItem(leftSym, rightSym));
					if (this.syms[leftSym].token == this.ExtStartToken)
						this.startProd = this.prods.length - 1;
				}
			}
		}
	}
	//根据字符串找到其在syms中的index，如果找到返回index，如果没有找到返回-1
	findSymIndexByToken(token) {
		for (let i = 0; i < this.syms.length; ++i) {
			if (this.syms[i].token == token) {
				return i;
			}
		}
		return -1;
	}
	getFirstOfNonTrm() {
		let changed;
		// eslint-disable-next-line no-constant-condition
		while (true) {
			changed = false;
			for (let i = 0; i < this.nonTrms.length; i++) {
				for (let j = 0; j < this.prods.length; j++) {
					if (this.prods[j].leftSym != this.nonTrms[i])
						continue;
					let it = 0;
					if (
						this.trms.indexOf(this.prods[j].rightSym[it]) !=
						-1 ||
						this.syms[this.prods[j].rightSym[it]].type ==
						SymType.Epsilon
					) {
						if (
							this.syms[this.nonTrms[i]].firstSet.indexOf(
								this.prods[j].rightSym[it]
							) == -1
						) {
							this.syms[this.nonTrms[i]].firstSet.push(
								this.prods[j].rightSym[it]
							);
							changed = true;
						}
						continue;
					}
					let flag = true;
					for (; it < this.prods[j].rightSym.length; ++it) {
						if (
							this.trms.indexOf(this.prods[j].rightSym[it]) != -1
						) {
							changed =
								changed ||
								this.mergeSetExceptEmpty(
									this.syms[this.nonTrms[i]].firstSet,
									this.syms[this.prods[j].rightSym[it]].firstSet,
									this.findSymIndexByToken(this.EpsilonToken)
								);
							flag = false;
							break;
						}
						changed =
							changed ||
							this.mergeSetExceptEmpty(
								this.syms[this.nonTrms[i]].firstSet,
								this.syms[this.prods[j].rightSym[it]].firstSet,
								this.findSymIndexByToken(this.EpsilonToken)
							);
						flag =
							flag &&
							this.syms[this.prods[j].rightSym[it]].firstSet.indexOf(
								this.findSymIndexByToken(this.EpsilonToken)
							) != -1;
						if (!flag) break;
					}
					if (flag && it == this.prods[j].rightSym.length) {
						if (
							this.syms[this.nonTrms[i]].firstSet.indexOf(
								this.findSymIndexByToken(this.EpsilonToken)
							) != -1
						) {
							this.syms[this.nonTrms[i]].firstSet.push(
								this.findSymIndexByToken(this.EpsilonToken)
							);
							changed = true;
						}
					}
				}
			}
			if (!changed) break;
		}
	}
	getFirstOfString(str) {
		let firstSet = [];
		if (str.length == 0) {
			return firstSet;
		}
		let epsilonIn = true;

		for (let it = 0; it < str.length; it++) {
			if (this.syms[str[it]].type == SymType.Trm) {
				this.mergeSetExceptEmpty(
					firstSet,
					this.syms[str[it]].firstSet,
					this.findSymIndexByToken(this.EpsilonToken)
				);
				epsilonIn = false;
				break;
			}
			if (this.syms[str[it]].type == SymType.Epsilon) {
				firstSet.push(str[it]);
				epsilonIn = false;
				break;
			}
			this.mergeSetExceptEmpty(
				firstSet,
				this.syms[str[it]].firstSet,
				this.findSymIndexByToken(this.EpsilonToken)
			);
			epsilonIn =
				epsilonIn &&
				this.syms[str[it]].firstSet.indexOf(
					this.findSymIndexByToken(this.EpsilonToken)
				) != -1;
			if (!epsilonIn) break;
		}
		if (epsilonIn)
			firstSet.push(this.findSymIndexByToken(this.EpsilonToken));
		return firstSet;
	}
	mergeSetExceptEmpty(des, src, epsilonIndex) {
		let changed = false;
		for (let i = 0; i < src.length; ++i) {
			if (src[i] != epsilonIndex && des.indexOf(src[i]) == -1) {
				des.push(src[i]);
				changed = true;
			}
		}
		return changed;
	}
}

export { SymType, err_code, errString, Grammar }