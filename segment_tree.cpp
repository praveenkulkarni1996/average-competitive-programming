/* Author: Praveen Kulkarni (eigenvalue)
 * Created: 2018-12-13 10:46
 * Copyright (C) 2018 pkulkarni <praveenkulkarni1996@gmail.com>
 */
#include <numeric>
#include <iomanip>
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstring>
#include <iostream>
#include <fstream>
#include <sstream>
#include <array>
#include <bitset>
#include <deque>
#include <forward_list>
#include <functional>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;

#define int long long
#define endl '\n'

template<class L, class R> ostream &operator<<(ostream &os, pair<L,R> P) {
  return os << "(" << P.first << "," << P.second << ")";
}
template<class T> ostream &operator<<(ostream& os, vector<T> V) {
  os << "["; for (auto vv : V) os << vv << ","; return os << "]";
}
template<class K, class X> ostream &operator<<(ostream& os, map<K,X> V) {
  os << "["; for (auto vv : V) os << vv << ","; return os << "]";
}

void debug_out() { cerr << endl; }

template <typename Head, typename... Tail>
void debug_out(Head H, Tail...T) {
  cerr << " " << H;
  debug_out(T...);
}

#ifdef LOCAL
#define debug(...) cerr << "[" << #__VA_ARGS__ << "]:", debug_out(__VA_ARGS__)
#else
#define debug(...) 42
#endif

using ii = pair<int, int>;
using vi = vector<int>;
using vii = vector<ii>;
using vvi = vector<vi>;
using vvii = vector<vii>;

class dsu {
  vector<int32_t> p;
  vector<int32_t> rank;

public:
  dsu(int n_): p(n_), rank(n_) {
    iota(p.begin(), p.end(), 0);
  }

  inline int32_t findset(int32_t x) {
    if(x != p[x]) {
      p[x] = findset(p[x]);
    }
    return p[x];
  };

  inline bool unite(int x, int y) {
    x = findset(x);
    y = findset(y);
    if(x == y) return false;
    if(rank[x] > rank[y]) {
      p[x] = y;
    } else {
      p[y] = x;
    }
    return true;
  }
};

struct SegmentTree {
private:
  const int n;
  const int root = 1;
  vector<int32_t> t;
  vector<bool> lazy;
  dsu &dsu_;

  inline int32_t pull(int32_t a, int32_t b) {
    return (a > -1 and b > -1 and dsu_.findset(a) == dsu_.findset(b))
      ? dsu_.findset(a)
      : -1;
  }

  void build(int p, int ll, int rr) {
    if(ll == rr) { // build the leaf nodes here
      t[p] = ll;
      return;
    }
    int mid = (ll + rr) / 2;
    build(2*p, ll, mid);
    build(2*p+1, mid+1, rr);
    t[p] = pull(t[2*p], t[2*p+1]);
  }

  void push(int p, int ll, int rr) {
    if(ll == rr or lazy[p] == false) return;
    int mid = (ll + rr) / 2;
    modify(p<<1, ll, mid, ll, rr, t[p]);     // modify with the data item
    modify(p<<1|1, mid+1, rr, ll, rr, t[p]); // modify with the data item
    t[p] = pull(t[p<<1], t[p<<1|1]);
    lazy[p] = false;
  }

  int32_t get(int p, int ll, int rr, int ql, int qr) {
    push(p, ll, rr);
    int32_t &cur = t[p];
    if(ql <= ll and rr <= qr) {
      return cur;
    }
    int mid = (ll + rr) / 2;
    if(qr <= mid) return get(2*p, ll, mid, ql, qr);
    if(mid < ql)  return get(2*p+1, mid+1, rr, ql, qr);
    return pull(get(2*p, ll, mid, ql, qr), get(2*p+1, mid+1, rr, ql, qr));
  }

  void modify(int p, int ll, int rr, int ql, int qr, int val) {
    if(qr < ll or rr < ql) return;
    int32_t &cur = t[p];
    push(p, ll, rr);
    if(ql <= ll and rr <= qr and cur > -1) {
      // apply the update value to the cur node
      dsu_.findset(cur);
      dsu_.unite(cur, val);
      // lazy[p] = true; (should uncomment if you need lazy propogation)
      return;
    }
    int mid = (ll + rr) / 2;
    modify(2*p, ll, mid, ql, qr, val);
    modify(2*p+1, mid+1, rr, ql, qr, val);
    cur = pull(t[2*p], t[2*p+1]);
  }
public:
  // default constructor
  SegmentTree(int n_, dsu &dsu_): n(n_), t(4 * n), lazy(4 * n, false), dsu_(dsu_) { 
    build(1, 0, n-1);
  }

  int32_t get(int ql, int qr) {
    return get(1, 0, n - 1, ql, qr);
  }

  void modify(int ql, int qr, int val) {
    modify(1, 0, n - 1, ql, qr, val);
  }
};

int32_t main() {
  ios::sync_with_stdio(0); cin.tie(0); cout.tie(0);
  int n, q; cin >> n >> q;
  dsu dsu_(n);
  SegmentTree st(n, dsu_);
  for(int i = 0; i < q; ++i) {
    int type; cin >> type;
    int x, y; cin >> x >> y;
    x--, y--;
    if(type == 1) {
      int32_t s1 = st.get(x, x);
      int32_t s2 = st.get(y, y);
      dsu_.unite(s1, s2);
    }
    else if(type == 2) {
      int32_t s1 = st.get(x, x);
      st.modify(x, y, s1);
    }
    else if(type == 3) {
      int32_t s1 = st.get(x, x);
      int32_t s2 = st.get(y, y);
      cout << ((dsu_.findset(s1) == dsu_.findset(s2)) ? "YES" : "NO") << endl;
    }
  }
}
