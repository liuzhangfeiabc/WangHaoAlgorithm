#include<bits/stdc++.h>
using namespace std;
inline void _wrong(){
	cout<<"无效输入";
	exit(0);
}
string s;
vector<string> mtby; 
map<string,int> mp;
int n;
struct node{
	int x;
	node *ls,*rs;
	bool hf;
	inline node(int _x = 0,node *_ls = 0,node *_rs = 0,bool _hf = 0){
		x = _x;ls = _ls;rs = _rs;hf = _hf;
	}
};
stack<node*> s1;
set<int> s2;
void dfs(node *q,bool fg = 0){
	if(q == 0) return;
	if(!fg && q -> x < -1) cout<<'(';
	dfs(q -> ls);
	if(q -> x < 0) cout<<" !&|>="[-(q -> x)]; 
	else cout<<mtby[(q -> x) - 1];
	dfs(q -> rs);
	if(!fg && q -> x < -1) cout<<')';
}
int step;
void out(vector<node*> left,vector<node*> right,int fr,int fs){
	cout<<"步骤("<<++step<<") {";
	for(int i = 0;i < left.size();++i) dfs(left[i],1),cout<<"; ";
	cout<<"} s==> {";
	for(int i = 0;i < right.size();++i) dfs(right[i],1),cout<<"; ";
	cout<<"} ";
	if(fr){
		cout<<"  ( ("<<fr<<") ";
		if(fs <= 5) cout<<" !&|>="[fs]<<" => )";
		else cout<<"=> "<<" !&|>="[fs - 5]<<" )";
	}
	cout<<endl;
}
bool wanghao(vector<node*> left,vector<node*> right,int fr = 0,int fs = 0){
	out(left,right,fr,fs);int nst = step;
	for(int i = 0;i < left.size();++i) if(left[i] -> x == -1){//! =>
		right.push_back(left[i] -> rs);
		swap(left[i],left[left.size() - 1]);left.pop_back();
		return wanghao(left,right,nst,1);
	}
	for(int i = 0;i < right.size();++i) if(right[i] -> x == -1){//=> !
		left.push_back(right[i] -> rs);
		swap(right[i],right[right.size() - 1]);right.pop_back();
		return wanghao(left,right,nst,6);
	}
	for(int i = 0;i < left.size();++i) if(left[i] -> x == -2){//& =>
		left.push_back(left[i] -> rs);left[i] = left[i] -> ls;
		return wanghao(left,right,nst,2);
	}
	for(int i = 0;i < right.size();++i)  if(right[i] -> x == -3){//=> |
		right.push_back(right[i] -> rs);right[i] = right[i] -> ls;
		return wanghao(left,right,nst,8);
	} 
	for(int i = 0;i < right.size();++i)  if(right[i] -> x == -4){//=> >
		left.push_back(right[i] -> ls);right[i] = right[i] -> rs;
		return wanghao(left,right,nst,9);
	}
	for(int i = 0;i < right.size();++i)  if(right[i] -> x == -2){//=> &
		node *p = right[i];
		right[i] = p -> ls;
		if(!wanghao(left,right,nst,7)) return 0;
		right[i] = p -> rs;
		return wanghao(left,right,nst,7);
	}
	for(int i = 0;i < left.size();++i) if(left[i] -> x == -3){//| =>
		node *p = left[i];
		left[i] = p -> ls;
		if(!wanghao(left,right,nst,3)) return 0;
		left[i] = p -> rs;
		return wanghao(left,right,nst,3);
	} 
	for(int i = 0;i < left.size();++i) if(left[i] -> x == -4){//> =>
		node *p = left[i];
		left[i] = p -> rs;
		if(!wanghao(left,right,nst,4)) return 0;
		swap(left[i],left[left.size() - 1]);left.pop_back();
		right.push_back(p -> ls);
		return wanghao(left,right,nst,4);
	}
	for(int i = 0;i < left.size();++i) if(left[i] -> x == -5){//= =>
		node *p = left[i];
		left[i] = p -> ls;left.push_back(p -> rs);
		if(!wanghao(left,right,nst,5)) return 0;
		left.pop_back();swap(left[i],left[left.size() - 1]);left.pop_back();
		right.push_back(p -> ls);right.push_back(p -> rs);
		return wanghao(left,right,nst,5);
	}
	for(int i = 0;i < right.size();++i)  if(right[i] -> x == -5){//=> =
		node *p = right[i];
		right[i] = p -> ls;left.push_back(p -> rs);
		if(!wanghao(left,right,nst,10)) return 0;
		left[left.size() - 1] = p -> ls;right[i] = p -> rs;
		return wanghao(left,right,nst,10);
	}
	s2.clear();
	for(int i = 0;i < left.size();++i) if(left[i] -> x > 0) s2.insert(left[i] -> x);
	for(int i = 0;i < right.size();++i) if(right[i] -> x > 0 && s2.find(right[i] -> x) != s2.end()){
		cout<<"步骤("<<nst<<")是公理"<<endl; 
		return 1;
	} 
	cout<<"步骤("<<nst<<")无法证明"<<endl;
	return 0;
}
#define chkzf(x) (((x) >= '0' && (x) <= '9') || ((x) >= 'A' && (x) <= 'Z') || ((x) >= 'a' && x <= 'z'))
int main(){
	cout<<"请输入待证的命题"<<endl;
	cout<<"用由数字、大写字母、小写字母组成的字符串表示不同的命题变元，!表示否定，&表示合取，|表示析取，>表示蕴含，=表示双蕴含"<<endl;
	cout<<"运算顺序为()!&|>="<<endl;
	cin>>s;
	for(int i = 0;i < s.size();++i){
		node *p = new node();
		if(s[i] == ')'){
			if(s1.empty()) _wrong();
			p = s1.top();s1.pop();
			while(1){
				if(s1.empty()) _wrong();
				node *ft = s1.top();s1.pop();
				if(ft -> x == -6) break;
				if(s1.empty()) _wrong();
				node *f2 = s1.top();s1.pop();
				ft -> ls = f2;ft -> rs = p;ft -> hf = (f2 -> hf) && (p -> hf);
				p = ft;
			}
			while(!s1.empty() && s1.top() -> x == -1){
				node *q = s1.top();s1.pop();
				q -> rs = p;q -> hf = p -> hf;
				p = q;
			}
			s1.push(p);
		}
		else if(chkzf(s[i])){
			string by;by.clear();by += s[i];
			while(i + 1 < s.size() && chkzf(s[i + 1])) by += s[++i];
			if(mp.find(by) == mp.end()) mp[by] = ++n,mtby.push_back(by);
			p -> x = mp[by];p -> hf = 1;
			while(!s1.empty() && s1.top() -> x == -1){
				node *q = s1.top();s1.pop();
				q -> rs = p;q -> hf = p -> hf;
				p = q;
			}
			s1.push(p);
		}
		else if(s[i] == '!'){
			p -> x = -1;
			s1.push(p);
		}
		else if(s[i] == '('){
			p -> x = -6;
			s1.push(p);
		}
		else{
			if(s[i] == '&') p -> x = -2;
			else if(s[i] == '|') p -> x = -3;
			else if(s[i] == '>') p -> x = -4;
			else if(s[i] == '=') p -> x = -5;
			else _wrong();
			if(s1.empty()) _wrong();
			node *q = s1.top();s1.pop();
			while(!s1.empty()){
				node *ft = s1.top();
				if((ft -> x) < (p -> x)) break;
				s1.pop();
				if(s1.empty()) _wrong();
				node *f2 = s1.top();s1.pop();
				ft -> ls = f2;ft -> rs = q;ft -> hf = (f2 -> hf) && (q -> hf);
				q = ft;
			}
			s1.push(q);s1.push(p);
		} 
	}
	if(s1.size() != 1){
		node *p = s1.top();s1.pop();
		if(p -> x == -6) _wrong(); 
		while(!s1.empty()){
			node *ft = s1.top();s1.pop();
			if(ft -> x == -6 || ft -> x > 0) _wrong(); 
			if(s1.empty()) _wrong();
			node *f2 = s1.top();s1.pop();
			if(f2 -> x == -6) _wrong(); 
			ft -> ls = f2;ft -> rs = p;ft -> hf = (f2 -> hf) && (p -> hf);
			p = ft;
		}
		s1.push(p);
	}
	if(!(s1.top() -> hf)) _wrong();
	cout<<"合法输入"<<endl;
	vector<node*> left,right;right.push_back(s1.top());
	if(wanghao(left,right)) cout<<"证明成功"<<endl;
	else cout<<"证明失败"<<endl;
	return 0;
}
