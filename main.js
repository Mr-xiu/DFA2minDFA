// DFA->最小化DFA   DFA->RG
// 编程语言：JavaScript(Node.js)
// 2020212259 何奕骁

// 导入文件系统模块(fs)
var fs = require("fs");

// DFA对象
var DFA = {
    initial_state: '',  // 起始状态名称
    final_states: {},  // 终止状态集名称集合
    states: {},  // 状态集
    writeStrRG: '',  // 写入文件的Str
    // 初始化DFA
    creat(data) {
        var dataLines = data.split(/\r?\n/);  // 按行读取
        var hasFinalState = false;
        dataLines.forEach((line) => {
            // 若为空行，则略过
            if (!line) return;
            lineData = line.split(/\s+/);
            // 若为首行
            if (lineData[0] === '0' && lineData[1] === '1') {
                console.log('读入DFA');
                return;
            }
            // 输入方式有误
            else if (lineData.length != 3) {
                console.log('输入格式有误！！！');
                return;
            }
            // 若读入起始状态
            else if (lineData[0].charAt(0) === '#') {
                this.initial_state = lineData[0].substr(1);
                this.states[this.initial_state] = {
                    0: lineData[1],
                    1: lineData[2],
                }
            }
            // 若读入终止状态
            else if (lineData[0].charAt(0) === '*') {
                hasFinalState = true;
                this.final_states[lineData[0].substr(1)] = lineData[0].substr(1);
                this.states[lineData[0].substr(1)] = {
                    0: lineData[1],
                    1: lineData[2],
                }
            }
            // 若为中间状态
            else {
                this.states[lineData[0]] = {
                    0: lineData[1],
                    1: lineData[2],
                }
            }

        })
        if (!this.initial_state) {
            console.log('输入格式有误: 没有起始状态');
            return;
        } else if (!hasFinalState) {
            console.log('输入格式有误: 没有终止状态');
            return;
        }

        // 去除不可达状态
        this.deleteUnreachableState();
    },
    // 去除不可达状态
    deleteUnreachableState() {
        // 可达状态表
        var canVisitTable = {};

        // 深度优先算法进行标记
        var dfs = (state) => {
            canVisitTable[state] = true;
            if (!canVisitTable[this.states[state]['0']]) dfs(this.states[state]['0']);
            if (!canVisitTable[this.states[state]['1']]) dfs(this.states[state]['1']);
        };
        dfs(this.initial_state);

        // 删除不可达状态
        for (var state in this.states) {
            if (!canVisitTable[state]) {
                delete this.states[state];
            }
        }
    },
    // 转换为RG
    toRG() {
        this.writeStrRG = '';
        // 先输出起始状态
        this.writeRGPrpduction(this.initial_state);
        // 遍历状态
        for (var state in this.states) {
            if (state !== this.initial_state || this.final_states[state]) {
                this.writeRGPrpduction(state);
            }
        }
        fs.writeFile('result_RG.txt', this.writeStrRG, function (err) {
            if (err) {
                return console.error('写入result_RG.txt失败：', err);
            }
        });
    },
    // 打印RG的产生式
    writeRGPrpduction(state) {
        var s = state + '->0' + (this.states[state]['0']) + '|1' + (this.states[state]['1']);
        if (this.final_states[this.states[state]['0']]) s += '|0';
        if (this.final_states[this.states[state]['1']]) s += '|1';
        this.writeStrRG += s + '\n';
    },

    // 可区分状态表
    disStateTable: {},

    // 状态对关联表
    associationTable: [],

    itialIndex: -1,
    minDFAStates: [],  // minDFA的状态集
    // DFA的极小化算法
    minimizationDFA() {
        for (var q in this.states) {
            this.disStateTable[q] = {};
            for (var p in this.states) {
                this.disStateTable[q][p] = false;
            }
        }

        // F与Q-F中的状态对肯定可区分
        for (var finalState in this.final_states) {
            // console.log(finalState);
            for (var state in this.states) {
                if (!this.final_states[state]) {
                    this.disStateTable[finalState][state] = true;
                    this.disStateTable[state][finalState] = true;
                }
            }
        }
        for (var q in this.states) {
            for (var p in this.states) {
                // p,q不相等且需均属于Q-F或F
                if (q != p && ((this.final_states[q] && this.final_states[p]) || !(this.final_states[q] || this.final_states[p])) && (!this.disStateTable[q][p])) {
                    // 若存在a，有δ(q,a),δ(p,a)已经被标记
                    if (this.disStateTable[this.states[q]['0']][this.states[p]['0']] || this.disStateTable[this.states[q]['1']][this.states[p]['1']]) {
                        if (!this.disStateTable[p])
                            this.disStateTable[p] = {};
                        if (!this.disStateTable[q])
                            this.disStateTable[q] = {};
                        // 标记可区分状态表中的表项(q,p)
                        this.disStateTable[q][p] = true;
                        this.disStateTable[p][q] = true;

                        // 递归地标记本次被标记的状态对的关联表上的各个状态对在可区分状态表中的对应表项
                        dfsHelper = (p, q) => {
                            for (var i = 0; i < this.associationTable.length; i++) {
                                if (this.associationTable[i].pair[q] && this.associationTable[i].pair[p]) {
                                    for (var k = 0; k < this.associationTable[i].list.length; k++) {
                                        this.disStateTable[this.associationTable[i].list[k][0]][this.associationTable[i].list[k][1]] = true;
                                        this.disStateTable[this.associationTable[i].list[k][1]][this.associationTable[i].list[k][0]] = true;
                                        dfsHelper(this.associationTable[i].list[k][0], this.associationTable[i].list[k][1]);
                                    }
                                }
                            }
                        }
                        dfsHelper(p, q);
                    }
                    else {
                        // a = '0' or '1'
                        for (a in this.states[q]) {
                            // 若δ(q,a)≠δ(p,a)且(q,p)与(δ(q,a),δ(p,a))不是同一个状态对
                            if (this.states[q][a] !== this.states[p][a]) {
                                var flag = false;
                                for (var i = 0; i < this.associationTable.length; i++) {
                                    if (this.associationTable[i].pair[this.states[q][a]] && this.associationTable[i].pair[this.states[p][a]]) {
                                        var tempPair = [0, 0];
                                        tempPair[0] = q;
                                        tempPair[1] = p;
                                        this.associationTable[i].list.push(tempPair)
                                        flag = true;
                                    }
                                    if (flag === true) break;
                                }
                                if (!flag) {
                                    var tempObj = {
                                        'pair': {},
                                        'list': [],
                                    };
                                    tempObj.pair[this.states[q][a]] = true;
                                    tempObj.pair[this.states[p][a]] = true;
                                    var tempPair = [0, 0];
                                    tempPair[0] = q;
                                    tempPair[1] = p;
                                    tempObj.list.push(tempPair)
                                    this.associationTable.push(tempObj);
                                }
                            }
                        }
                    }
                }
            }
        }
    },

    // 转换成最小化DFA
    toMinDFA() {
        this.minimizationDFA();
        console.log(this.disStateTable);
        console.log(this.associationTable[1])
        var hasVisit = {};
        // 深度优先遍历来初始化minDFAStates
        var dfs = (p) => {
            hasVisit[p] = true;
            var ans = [p];
            for (var q in this.disStateTable[p]) {
                if (q !== p && !hasVisit[q] && !this.disStateTable[p][q]) {
                    ans = ans.concat(dfs(q));
                }
            }
            return ans;
        };

        // 初始化minDFAStates
        for (var p in this.disStateTable) {
            if (!hasVisit[p]) {
                var isFinal = this.final_states[p] ? true : false;
                var tempObj = {
                    'list': [],
                    isFinal: isFinal,  // 是否为终止状态
                }
                tempObj.list = dfs(p);

                this.minDFAStates.push(tempObj);
                for (var i = 0; i < this.minDFAStates[this.minDFAStates.length - 1].list.length; i++) {
                    if (this.minDFAStates[this.minDFAStates.length - 1].list[i] === this.initial_state) {
                        this.itialIndex = this.minDFAStates.length - 1;
                    }
                }

            }
        }
        for (var i = 0; i < this.minDFAStates.length; i++) {
            var p = this.minDFAStates[i].list[0];

            var list0 = [];
            var list1 = [];
            for (var k = 0; k < this.minDFAStates.length; k++) {
                for (var t = 0; t < this.minDFAStates[k].list.length; t++) {
                    if (this.states[p]['0'] === this.minDFAStates[k].list[t]) {
                        list0 = this.minDFAStates[k].list;
                    }
                    if (this.states[p]['1'] === this.minDFAStates[k].list[t]) {
                        list1 = this.minDFAStates[k].list;
                    }
                }
            }

            this.minDFAStates[i]['0'] = list0;
            this.minDFAStates[i]['1'] = list1;
        }
        this.writeMinDFA();
    },

    // 打印MinDFA
    writeMinDFA() {
        var str = '0 1\n';
        var help = (i, inItial) => {
            if (!inItial && i === this.itialIndex) return '';
            var tempStr = '[';

            if (this.minDFAStates[i].isFinal && !inItial) tempStr = '*[';
            else if (inItial) tempStr = '#[';
            for (var k = 0; k < this.minDFAStates[i].list.length; k++) {
                if (k === 0) {
                    tempStr += this.minDFAStates[i].list[k];
                } else {
                    tempStr += ',' + this.minDFAStates[i].list[k];
                }

            }

            tempStr += '] [';
            for (var k = 0; k < this.minDFAStates[i]['0'].length; k++) {
                if (k === 0) {
                    tempStr += this.minDFAStates[i]['0'][k];
                } else {
                    tempStr += ',' + this.minDFAStates[i]['0'][k];
                }
            }
            tempStr += '] [';
            for (var k = 0; k < this.minDFAStates[i]['1'].length; k++) {
                if (k === 0) {
                    tempStr += this.minDFAStates[i]['1'][k];
                } else {
                    tempStr += ',' + this.minDFAStates[i]['1'][k];
                }
            }
            tempStr += ']\n';
            return tempStr;
        }

        // 打印起始状态
        str += help(this.itialIndex, true);

        // 打印其他状态
        for (var i = 0; i < this.minDFAStates.length; i++) {
            str += help(i, false);
        }

        fs.writeFile('result_MinDFA.txt', str, function (err) {
            if (err) {
                return console.error('写入result_MinDFA.txt失败：', err);
            }
        });
    },
}

// 异步读入输入的DFA
fs.readFile('input.txt', function (err, data) {
    if (err) {
        return console.error('读取input.txt失败：', err);
    }
    DFA.creat(data.toString());  // 初始化DFA
    DFA.toRG();  // 将DFA转换为RG
    DFA.toMinDFA();  // 将DFA转换为最小化DFA
});

/*
测试1：
0 1
#q0 q1 q2
q1 q0 q3
*q2 q4 q5
*q3 q4 q5
*q4 q4 q5
q5 q5 q5

测试2：
0 1
#q0 q1 q5
q1 q5 q2
q2 q3 q6
q3 q2 q4
*q4 q8 q1
q5 q1 q6
q6 q7 q2
q7 q6 q8
*q8 q5 q4
q9 q7 q5
*/
