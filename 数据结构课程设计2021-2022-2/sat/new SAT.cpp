#include "a.h"
#include <time.h>
#include <unordered_map>
#include <map>

using namespace std;

string createSudokuToFile(int holes);								  //根据holes来挖洞
void createSudoku(int cnfSolution[9][9]);							  //生成数独终盘
void randomFirstRow(int row[9]);									  //随机生成第一行
void createStartinggrid(const int a[][9], int b[][9], int numDigits); //随机生成初盘
bool Digit(int a[][9], int i, int j);								  //递归生成后i行
void showsudoku(int a[][9]);										  //打印数独数组
string toCnf(int a[][9], int holes);								  //转换成CNF文件
void showResults(string ptr,double time);										  //将数独棋盘的解res文件转化为数独棋盘

class CnfParser
{
public:
	CnfParser(){ clause = new Deque<int>();};
	~CnfParser();
	bool readfile(string s);						//读文件
	bool SAT();										
	void back_pop();								//还原状态
	bool SATzj(int wid, bool youhua);				//解决SAT问题
	void outfileHash(string s, bool type, double time); //输出结果（哈希表）

private:
	int boolsize = 0;		//变元数量
	int clauseSize = 0; //子句数量
	crossListNode *root = nullptr;
	unordered_map<int, nodeUphead *> vmap = {};
	bool jie = true;
	Deque<int> *clause = nullptr;		 //单子句队列
	Deque<int> *back = new Deque<int>(); //栈(用来回溯)
};

CnfParser::~CnfParser()
{
	if (clause != nullptr)
	{
		delete clause;
		clause = nullptr;
	}
	if (back != nullptr)
	{
		delete back;
		back = nullptr;
	}
	while (root)
	{
		crossListNode *zjdel = root;
		root = root->down;
		while (zjdel)
		{
			crossListNode *del = zjdel;
			zjdel = zjdel->right;
			delete del;
		}
	}
}

bool CnfParser::readfile(string s)
{
	string c, cnf;
	int nodesize = 0, zjsize = 0;
	char ccc[161];
	ifstream inFile(s, ios::in);
	if (!inFile)
	{
		cout << "地址错误\n";
		inFile.close();
		return false;
	}
	inFile >> c;
	while (c == "c")
	{
		inFile.getline(ccc, 160);
		inFile >> c;
	}
	inFile >> cnf >> nodesize >> zjsize;
	boolsize = nodesize;
	clauseSize = zjsize;
	crossListNode *addlist = nullptr; //每个子句头节点(上一个)
	crossListNode *addnode = nullptr; //子句添加上的节点

	for (int i = 0; i < clauseSize; i++)
	{
		if (i == 0)
			root = addnode = addlist = new crossListNode();
		else
			addnode = new crossListNode(addlist);
		int text;
		addlist = addnode;
		inFile >> text;
		int sum = 0;
		int dz = 0;
		while (text != 0)
		{
			sum++;
			int d = text;
			inFile >> text;
			int id = d > 0 ? d : -d;
			dz = d;
			
			if (vmap.find(id) == vmap.end())		//判断变元是否在map中
			{										//不在map中，则添加
				new crossListNode(addnode, d);		//添加行文字节点
				addnode = addnode->right;			//右移到新添加的节点
				nodeUphead *add = new nodeUphead(); //添加变元列头节点
				add->begin = add->fail = addnode;	//设置变元列头节点的头节点和尾节点指针
				add->leng++;						//变元列的长度加1
				vmap[id] = add;						//添加到map中
			}
			else
			{												   //在map中
				new crossListNode(vmap[id]->fail, addnode, d); //添加行文字节点
				addnode = addnode->right;					   //右移到新添加的节点
				vmap[id]->fail = addnode;					   //设置变元列尾节点
				vmap[id]->leng++;							   //变元列的长度加1
			}

		}
		if (sum == 1)
		{
			if (dz > 0)
			{
				vmap[dz]->danzj = true;
				clause->push_back(dz);
				vmap[dz]->falseTrue = true;
			}
			else
			{
				vmap[-dz]->danzj = true;
				clause->push_back(-dz);
				vmap[-dz]->falseTrue = false;
			}
		}
	}
	inFile.close();
	return true;
}

bool CnfParser::SAT()
{
	int chulizj = 0;
	crossListNode *nodeptr = root;
	Deque<int> dui;
	bool type = true;
	while (!clause->empty())
	{ //对文件原有的单子句处理,不需要回溯(不入栈)
		bool a = false;
		int id = clause->front();
		clause->pop_front();
		if (vmap[id]->type)
		{
			continue;
		}
		a = SATzj(id, true);
		if (!a)
		{
			return false;
		}
	}
	while (type)
	{
		bool huishu = true; //回溯标记
		int id = 0;
		while (!clause->empty() && huishu)
		{
			id = clause->front();
			clause->pop_front();
			if (vmap[id]->type)
				continue;
			vmap[id]->danzj = true;
			huishu = SATzj(id, false);
		}
		if (huishu)
		{
			id = 0;
			//遍历map，找到未被访问的变元，且最大的变元
			for (auto it = vmap.begin(); it != vmap.end(); it++)
			{
				if (!it->second->type && !it->second->danzj)
				{
					if (id == 0)
					{
						id = it->first;
					}
					else
					{
						if (it->second->leng > vmap[id]->leng)
						{
							id = it->first;
						}
					}
				}
			}
			if (id == 0)
			{ //处理完,结束处理
				return true;
			}
			vmap[id]->falseTrue = false;
			huishu = SATzj(id, false);
		}
		else
		{
			while (!huishu)
			{ //回溯
				while (!clause->empty())
				{
					clause->pop_front();
				}
				if (back->empty())
					return false;
				int backid = back->back();
				while (vmap[backid]->danzj)
				{ //单子句
					back_pop();
					backid = back->back();
				}
				if (vmap[backid]->falseTrue)
				{
					vmap[backid]->falseTrue = false;
					back_pop();
				}
				else
				{
					vmap[backid]->falseTrue = true;
					back_pop();
					huishu = SATzj(backid, false);
				}
			}
		}
	}
	return true;
}

void CnfParser::back_pop()
{								//还原状态
	int back_id = back->back(); //回溯对象的编号
	vmap[back_id]->type = false;
	crossListNode *clauseSize = vmap[back_id]->begin;
	if (vmap[back_id]->danzj)
	{
		vmap[back_id]->danzj = false;
		vmap[back_id]->falseTrue = false;
	}
	while (clauseSize)
	{
		crossListNode *zjHead = clauseSize;
		while (zjHead->left != nullptr)
		{
			zjHead = zjHead->left;
		}
		if (zjHead->id == back_id)
		{ //子句因为当前文字而消除
			zjHead->falseTrue = false;
			zjHead->id = 1e9;
			zjHead = zjHead->right;
			while (zjHead)
			{
				int id = zjHead->id > 0 ? zjHead->id : -(zjHead->id);
				vmap[id]->leng++;
				zjHead = zjHead->right;
			}
		}
		clauseSize->falseTrue = false;
		clauseSize = clauseSize->down;
	}
	back->pop_back();
}

bool CnfParser::SATzj(int wid, bool youhua)
{
	int id = wid;
	crossListNode *beg = vmap[id]->begin;
	bool falseTrue = vmap[id]->falseTrue;
	vmap[id]->type = true;
	bool type = true;
	while (beg)
	{
		crossListNode *head = beg;
		while (head->left != nullptr)
		{ //子句的头节点
			head = head->left;
		}
		beg->falseTrue = true;
		if (head->falseTrue)
		{ //子句已经被消除的情况
			beg = beg->down;
			continue;
		}
		else
		{
			if (beg->id > 0 && !falseTrue || beg->id < 0 && falseTrue)
			{ //消去文字的情况
				int leng = 0, danid = 0;
				head = head->right;
				while (head)
				{
					if (!head->falseTrue)
					{
						leng++;
						danid = head->id;
					}
					head = head->right;
				}
				if (leng == 0)
					type = false; //全部消去(回溯)
				else if (leng == 1)
				{ //单子句
					if (danid > 0)
					{ //正文字
						vmap[danid]->falseTrue = true;
						clause->push_back(danid);
					}
					else
					{
						vmap[-danid]->falseTrue = false;
						clause->push_back(-danid);
					}
				}
			}
			else if (beg->id < 0 && !falseTrue || beg->id > 0 && falseTrue)
			{
				head->id = id;
				head->falseTrue = true;
				head = head->right;
				while (head)
				{
					int vid = head->id > 0 ? head->id : -head->id;
					vmap[vid]->leng--;
					head = head->right;
				}
			}
			beg = beg->down;
		}
	}
	if (!youhua)
	{
		back->push_back(id);
	}
	return type;
}

void CnfParser::outfileHash(string s, bool type, double time)
{ //哈希表转化为表（k从无序变有序）
	map<int, nodeUphead *> mp;
	for (auto it = vmap.begin(); it != vmap.end(); it++)
	{
		mp[it->first] = it->second;
	}
	string ss = s;
	ss.erase(s.length() - 4);
	ss = ss + ".res";
	ofstream inFile(ss, ios::out);
	if (inFile)
	{
		inFile << "s ";

		if (type)
		{
			inFile << "1\n" << "v";
			//遍历vmap输出fasleTrue,false输出负文字，true输出正文字
			for (auto it = mp.begin(); it != mp.end(); it++)
			{
				if (it->second->falseTrue)
				{
					inFile << " " << it->first;
				}
				else
				{
					inFile << " -" << it->first;
				}
			}
			inFile << "\n";
		}
		else
		{
			inFile << "0\n" << "v\n";
		}
		inFile << "t " << time;
	}
	inFile.close();
}

int main()
{
	CnfParser *cnfSolution = nullptr;
	CnfParser *sudokuGame = nullptr;
	string filePtr;
	string ss;
	bool type = false;
	double time;
	int op = 1;
	while (op)
	{
		system("cls");
		cout << endl << endl;
		cout << "\t\t    CnfParser or SudokuGame\n";
		cout << "\t++++++++++++++++++++++++++++++++++++++++++++++++++\n";
		cout << "\t\t1.CnfParser\t\t2.SudokuGame\n";
		cout << "\t\t\t\t0.Exit\n";
		cout << "\t++++++++++++++++++++++++++++++++++++++++++++++++++\n";
		cin >> op;
		system("cls");
		switch (op)
		{
		case 1:
			type = false;
			time = 0;
			cnfSolution = new CnfParser();
			cout << "输入文件地址:";
			cin >> filePtr;
			if (cnfSolution->readfile(filePtr))
			{
				clock_t start, finish; //开始,结束时间
				start = clock();
				type = cnfSolution->SAT();
				finish = clock();
				time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
				cnfSolution->outfileHash(filePtr, type, time);
				cout << "花费时间:" << time << "ms" << endl;
			}
			else
			{
				cout << "地址错误\n" << endl;
			}
			system("pause");
			delete cnfSolution;
			break;
		case 2:
			type = false;
			time = 0;
			sudokuGame = new CnfParser();
			cout << "输入初始棋盘的数字个数（17~81）：";
			int num, holes;
			cin >> num;
			holes = 81 - num;
			if (num < 17 || num > 81)
			{
				cout << "输入错误，请重新输入\n";
				system("pause");
				break;
			}
			clock_t start, finish; //开始,结束时间
			start = clock();
			filePtr = createSudokuToFile(holes);
			finish = clock();
			time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
			cout << "生成初期棋盘花费时间：" << time << "ms\n";
			if (sudokuGame->readfile(filePtr))
			{
				start = clock();
				type = sudokuGame->SAT();
				finish = clock();
				time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
				sudokuGame->outfileHash(filePtr, type, time);
				showResults(filePtr,time);
			}
			else
			{
				cout << "文件打开失败\n";
			}
			system("pause");
			delete sudokuGame;
			break;
		case 0:
			exit(0);
			break;
		default:
			cout << "\t\t\t输入错误，请重新输入(1~2)\n";
		}
	}
	return 0;
}

string createSudokuToFile(int holes)
{
	int cnfSolution[9][9] = {0};
	int starting_grid[9][9] = {0};
	//记录所花的时间
	clock_t start, finish;
	start = clock();
	createSudoku(cnfSolution); //生成数独终盘
	finish = clock();
	double time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
	cout << "生成数独终盘花费时间：" << time << "ms\n";
	start = clock();
	createStartinggrid(cnfSolution, starting_grid, holes); //随机生成初盘
	finish = clock();
	time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
	cout << "生成初盘花费时间：" << time << "ms\n";
	cout << "初始棋盘为:" << endl;
	showsudoku(starting_grid);
	start = clock();
	string filename = toCnf(starting_grid, holes); //转化为cnf文件
	finish = clock();
	time = ((double)(finish - start) / CLOCKS_PER_SEC) * 1000;
	cout << "转化为cnf文件花费时间：" << time << "ms\n";
	return filename;
}

void createSudoku(int cnfSolution[9][9])
{
	randomFirstRow(cnfSolution[0]);
	Digit(cnfSolution, 1, 0);
}

void randomFirstRow(int row[9])
{
	int i;
	bool flag[10] = {false};
	srand((unsigned)time(nullptr));
	for (i = 0; i < 9; i++)
	{
		int j = rand() % 9 + 1;
		if (!flag[j])
		{
			row[i] = j;
			flag[j] = true;
		}
		else
		{
			j = 1;
			while (flag[j])
			{
				j++;
			}
			row[i] = j;
			flag[j] = true;
		}
	}
}

/*
 *       递归生成后i行
 *       参数：int a[][COL]，数独数组；int i，行数；int j，列数
 *       返回值：true 成功 false 失败
 *       由左上开始，按照列填充，每列填充完毕，再填充下一列
 */

bool Digit(int a[][9], int i, int j)
{ //递归填充数独元素
	if (i < 9 && j < 9)
	{
		int x, y, k;
		bool check[9 + 1]; //用于排除已经使用过的的数字
		for (k = 0; k <= 9; k++)
		{
			check[k] = true;
		}
		for (x = 0; x < j; x++)
			check[a[i][x]] = false; //行使用过的数字置为false
		for (x = 0; x < i; x++)
			check[a[x][j]] = false; //列已使用的数字置为false
		for (x = i / 3 * 3; x <= i; x++)
		{ //宫使用过的数字置为false, x,y为宫的右下角坐标（边界）
			if (x == i)
				for (y = j / 3 * 3; y < j; y++)
					check[a[x][y]] = false;
			else
				for (y = j / 3 * 3; y < j / 3 * 3 + 3; y++)
					check[a[x][y]] = false;
		}

		bool flag = false;
		for (k = 1; k <= 9 && !flag; k++)
		{ //从check数组中查找安全的数字
			if (check[k] == true)
			{
				flag = true;
				a[i][j] = k;
				if (j == 9 - 1 && i != 9 - 1)
				{ //列填充完毕，填充下一列
					if (Digit(a, i + 1, 0) == true)
						return true;
					else
						flag = false;
				}
				else if (j != 9 - 1)
				{ //列不满，填充下一行
					if (Digit(a, i, j + 1) == true)
						return true;
					else
						flag = false;
				}
			}
		}
		if (!flag)
		{
			a[i][j] = 0;
			return false;
		}
	}
	return true;
}

void createStartinggrid(const int a[][9], int b[][9], int numDigits)
{ //随机生成初盘
	int i, j, k;
	srand((unsigned)time(nullptr));

	//复制棋盘
	for (i = 0; i < 9; i++)
		for (j = 0; j < 9; j++)
			b[i][j] = a[i][j];

	// int c[numDigits][2];
	// c为存放挖洞的坐标
	int **c = new int *[numDigits];
	for (int i = 0; i < numDigits; i++)
	{
		c[i] = new int[2];
	}
	int m, flag = 0;

	for (i = 0; i < numDigits; i++)
	{
		j = rand() % 9;
		k = rand() % 9;

		flag = 0;
		//判断是否已经挖洞
		for (m = 0; m < i; m++)
			if (j == c[m][0] && k == c[m][1])
				flag = 1;

		if (flag == 0)
		{
			b[j][k] = 0;
			c[i][0] = j;
			c[i][1] = k;
		}
		else
			i--;
	}
}

void showsudoku(int a[][9])
{
	for (int i = 0; i < 9; i++)
	{
		if (i % 3 == 0 && i != 0)
			cout << "\t━━━━━━╋━━━━━━╋━━━━━━━ " << endl;
		cout << "\t";
		for (int j = 0; j < 9; j++)
		{
			if (j % 3 == 0 && j != 0)
				cout << "┃";

			if (a[i][j] == 0)
				cout << " .";
			else
				cout << " " << a[i][j];
		}
		cout << endl;
	}
}

/*
 *   将数独棋盘转换为cnf文件
 *   参数：int a[][9]，数独棋盘；int holes 挖洞个数
 */
string toCnf(int a[][9], int holes)
{
	ofstream outfile(".\\cnfSolution.cnf"); //输出文件
	if (!outfile.is_open())
		cout << "打开文件失败" << endl;
	//将棋盘以注释的形式输出
	outfile << "c 数独棋盘：" << endl;
	for (int i = 0; i < 9; i++)
	{
		if (i % 3 == 0 && i != 0)
			outfile << "c\t━━━━━━━╋━━━━━━━╋━━━━━━━━ " << endl;

		outfile << "c\t";

		for (int j = 0; j < 9; j++)
		{
			if (j % 3 == 0 && j != 0)
				outfile << "┃";

			if (a[i][j] == 0)
				outfile << " .";
			else
				outfile << " " << a[i][j];
		}
		outfile << endl;
	}
	outfile << "c" << endl;
	//第一行，第一个数字为变量个数，第二个数字为约束个数
	outfile << "p cnf 729 " << 8829 + 81 - holes << endl; 
	//第（x，y）格有初始值，生成单子句
	for (int x = 0; x < 9; ++x)
	{
		for (int y = 0; y < 9; ++y)
			if (a[x][y] != 0)
				outfile << (x + 1) * 100 + (y + 1) * 10 + a[x][y] << " " << 0 << endl;
	}
	// 每格只能有一个数字总约束（1~9）
	for (int x = 1; x <= 9; ++x)
	{
		for (int y = 1; y <= 9; ++y)
		{
			for (int z = 1; z <= 9; ++z)
				outfile << x * 100 + y * 10 + z << " ";
			outfile << 0 << endl;
		}
	}
	// 行约束
	for (int y = 1; y <= 9; ++y)
	{
		for (int z = 1; z <= 9; ++z)
			for (int x = 1; x <= 8; ++x)
				for (int i = x + 1; i <= 9; ++i)
					outfile << 0 - (x * 100 + y * 10 + z) << " "
							<< 0 - (i * 100 + y * 10 + z) << " " << 0 << endl;
	}
	// 列约束
	for (int x = 1; x <= 9; ++x)
	{
		for (int z = 1; z <= 9; ++z)
			for (int y = 1; y <= 8; ++y)
				for (int i = y + 1; i <= 9; ++i)
					outfile << 0 - (x * 100 + y * 10 + z) << " "
							<< 0 - (x * 100 + i * 10 + z) << " " << 0 << endl;
	}
	// 宫约束
	for (int z = 1; z <= 9; ++z)
	{
		for (int i = 0; i <= 2; ++i)
			for (int j = 0; j <= 2; ++j)
				for (int x = 1; x <= 3; ++x)
					for (int y = 1; y <= 3; ++y)
						for (int k = y + 1; k <= 3; ++k)
							outfile << 0 - ((3 * i + x) * 100 + (3 * j + y) * 10 + z) << " "
									<< 0 - ((3 * i + x) * 100 + (3 * j + k) * 10 + z) << " " << 0 << endl;
	}
	for (int z = 1; z <= 9; z++)
	{
		for (int i = 0; i <= 2; i++)
			for (int j = 0; j <= 2; j++)
				for (int x = 1; x <= 3; x++)
					for (int y = 1; y <= 3; y++)
						for (int k = x + 1; k <= 3; k++)
							for (int l = 1; l <= 3; l++)
								outfile << 0 - ((3 * i + x) * 100 + (3 * j + y) * 10 + z) << ' '
										<< 0 - ((3 * i + k) * 100 + (3 * j + l) * 10 + z) << ' ' << 0 << endl;
	}
	outfile.close();
	return ".\\cnfSolution.cnf"; //返回一个string类型的对象
}

void showResults(string ptr,double time)
{
	//将地址后缀改为.res
	string ss = ptr;
	ss.replace(ss.end() - 4, ss.end(), ".res");
	ifstream infile(ss);
	if (!infile.is_open())
		cout << "打开文件失败" << endl;
	else
	{
		char c;
		int a[9][9];
		infile >> c;
		if (c == 's')
		{
			infile >> c;
			if (c == '1')
			{
				cout << "\n解出数独花费时间:" << time << "ms" << endl;
				cout << "解出的棋盘：\n";
				string s;
				infile >> c;
				int i,j,k;
				//判断s的第一位不为‘v’
				if (c == 'v')
				{
					infile >> s;
					while (s.at(0) != 't')
					{//将s中的数字转换为整数
						int num = 0;
						num = atoi(s.c_str());
						if (num > 0)
						{
							i = num / 100;
							j = (num % 100) / 10;
							k = num % 10;
							a[i - 1][j - 1] = k;
						}
						infile >> s;
					}
					showsudoku(a);
				}
			}
			else
				cout << "求解失败！" << endl;
		}
	}
	infile.close();
}