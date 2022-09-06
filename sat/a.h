#include<iostream>
#include<string>
#include<fstream>

using namespace std;

template<typename T>  //节点模板
struct listnode
{
public:
	listnode() :up(nullptr), down(nullptr) {};
	listnode(T data) :up(nullptr), data(data), down(nullptr) {};
	listnode(listnode* pup, T data) :up(pup), data(data), down(nullptr) {};
	listnode(T data, listnode* pdoen) :up(nullptr), data(data), down(pdoen) {};
	listnode(listnode* pup, T data, listnode* pdoen) :up(pup), data(data), down(pdoen) {};
	listnode* up;
	listnode* down;
	T data;
};

template<class T>
class Deque    //双向链表
{
public:
	Deque()
	{
		head = new listnode<T>();
		tail = new listnode<T>();
		head->down = tail;
		tail->up = head;
		size = 0;
	};
	Deque(const Deque& d)
	{
		d.cop(this);
	};

	~Deque();
	int getsize();
	void push_back(T data);   //在结尾添加
	void push_front(T data);	//在开头添加
	void pop_back();	//删除结尾
	void pop_front();	//删除开头
	void cop(Deque<T>& cop);	//复制函数
	void delarr();	//清空
	bool empty();	//判空
	T back();	//返回结尾
	T front();	//返回开头


	//遍历器
	class iterator
	{
	private:
		listnode<T>* ptr;
	public:

		iterator(listnode<T>* p = nullptr) : ptr(p) {};

		listnode<T>* getptr()
		{
			return ptr;
		}

		T& operator*() const {
			return *ptr;
		}

		listnode<T>* operator->() const {
			return ptr;
		}

		iterator& operator++() {
			ptr = ptr->down;
			return *this;
		}

		iterator operator++(int) {
			listnode<T>* tmp = ptr;
			// this 是指向list_iterator的常量指针，因此*this就是list_iterator对象，前置++已经被重载过
			++(*this);
			return iterator(tmp);
		}

		bool operator==(const iterator& t) const {
			return t.ptr == this->ptr;
		}

		bool operator!=(const iterator& t) const {
			return t.ptr != this->ptr;
		}
	};
	iterator begin()
	{
		return iterator(head->down);
	};
	iterator end()
	{
		return iterator(tail);
	};
	void emplace(iterator& prt, T data);	//添加节点到指定位置
	void del(iterator& prt);	//删除指定位置的节点

	//查找节点
	iterator find(T data)
	{
		for (iterator i = this->begin(); i != this->end(); i++)
		{
			if (i->data == data)
				return i;
		}
		return this->end();
	}
private:
	listnode<T>* head;  //队首
	listnode<T>* tail;  //队尾
	int size;
};

template<class T>
Deque<T>::~Deque()
{
	iterator en = end();
	iterator beg = begin();
	for (iterator it = beg; it != en;)
	{
		iterator itt = it;
		it++;
	}
	delete(head);
	delete(tail);
}

template<class T>
int Deque<T>::getsize()
{
	return size;
}

template<class T>
void Deque<T>::push_back(T data)
{
	listnode<T>* add = new listnode<T>(tail->up, data, tail);
	listnode<T>* pup = tail->up;
	pup->down = add;
	tail->up = add;
	size++;
}

template<class T>
void Deque<T>::push_front(T data)
{
	listnode<T>* add = new listnode<T>(head, data, head->down);
	listnode<T>* dow = head->down;
	dow->up = add;
	head->down = add;
	size++;
}

template<class T>
void Deque<T>::pop_back()
{
	listnode<T>* del = tail->up;
	listnode<T>* upn = del->up;
	upn->down = tail;
	tail->up = upn;
	delete(del);
	size--;
}

template<class T>
void Deque<T>::pop_front()
{
	listnode<T>* del = head->down;
	listnode<T>* dow = del->down;
	dow->up = head;
	head->down = dow;
	delete(del);
	size--;
}

/*
复制链表
*/
template<class T>
void Deque<T>::cop(Deque<T>& cop)
{
	for (Deque<T>::iterator i = this->begin(); i != this->end(); i++)
	{
		cop.push_back(i->data);
	}
	cop.size = this->size;
}

/*
清空链表
*/
template<class T>
void Deque<T>::delarr()
{
	int a = size;
	for (int i = 0; i < a; i++)
	{
		this->pop_front();
	}
}


/*
判空
*/
template<class T>
bool Deque<T>::empty()
{
	if (size == 0)
		return true;
	else
		return false;
}

template<class T>
T Deque<T>::back()
{
	return T(tail->up->data);
}

template<class T>
T Deque<T>::front()
{
	return T(head->down->data);
}


/*
添加元素
*/
template<class T>
void Deque<T>::emplace(iterator& prt, T data)
{
	listnode<T>* add = new listnode<T>(prt->up, data, prt.getptr());
	listnode<T>* pup = prt->up;
	pup->down = add;
	prt->up = add;
	size++;
	prt = iterator(add);
}

/*
根据遍历器删除对应节点
*/
template<class T>
void Deque<T>::del(iterator& prt)
{
	if (prt != this->begin() && prt != this->end())
	{
		prt->up->down = prt->down;
		prt->down->up = prt->up;
		iterator a = prt;
		prt++;
		size--;
		delete(a.getptr());
	}
}



struct crossListNode
{
	crossListNode() {};
	crossListNode(crossListNode* up)
	{
		this->up = up;
		this->up->down = this;
	};
	crossListNode(crossListNode* list, int data)
	{
		this->left = list;
		this->left->right = this;
		id = data;
	};
	crossListNode(crossListNode* up, crossListNode* list, int data)
	{
		this->up = up;
		this->left = list;
		id = data;
		this->up->down = this;
		this->left->right = this;
	};
	int id = 1e9;	//文字
	bool falseTrue = false;	//节点是否消除(子句是否消除)
	crossListNode* up = nullptr;		//上一个节点
	crossListNode* down = nullptr;	//下一个节点
	crossListNode* left = nullptr;	//左节点
	crossListNode* right = nullptr;	//右节点
};

struct nodeUphead
{
	nodeUphead() {};
	int leng = 0;//包含变元的长度
	bool falseTrue = false;//变元真假
	bool type = false;//是否处理
	bool danzj = false;
	crossListNode* begin = nullptr;//变元列的起始地址
	crossListNode* fail = nullptr;//变元列的结束地址
};

