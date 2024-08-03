#include<bits/stdc++.h>
using      namespace std ;
#define    int long long 
#define    FAST  ios_base::sync_with_stdio(0); cin.tie(NULL); cout.tie(NULL);
#define    TestCases int TOTALTC ; cin >> TOTALTC ; for(_case = 1 ; _case <=  TOTALTC ; _case++)
#define    rep(i,n) for (int i = 0; i < (n); ++i)
#define    all(x) (x).begin(), (x).end()
#define    nl "\n"
const      int INF = 1e18 ;


//////////// TARJANS ALGO

struct SCC {
    int V = 0;
    vector<vector<int>> adj;
    vector<int> tour_index, low_link;
    int tour;
 
    vector<int> stack;
    vector<bool> in_stack;
    int S = 0;
 
    vector<vector<int>> components;
    vector<int> which_component;
 
    SCC(int v = 0) {
        init(v);
    }
 
    SCC(const vector<vector<int>> &_adj) {
        init(_adj);
    }
 
    void init(int v) {
        V = v;
        adj.assign(V, {});
    }
 
    void init(const vector<vector<int>> &_adj) {
        adj = _adj;
        V = adj.size();
    }
 
    void add_edge(int a, int b) {
        adj[a].push_back(b);
    }
 
    // Tarjan's algorithm.
    void dfs(int node) {
        tour_index[node] = tour++;
        low_link[node] = tour_index[node];
        stack[S++] = node;
        in_stack[node] = true;
 
        for (int neighbor : adj[node])
            if (tour_index[neighbor] < 0) {
                // neighbor is part of our subtree.
                dfs(neighbor);
                low_link[node] = min(low_link[node], low_link[neighbor]);
            } else if (in_stack[neighbor]) {
                // neighbor is our tree ancestor, so it's a candidate for low_link.
                low_link[node] = min(low_link[node], tour_index[neighbor]);
            }
 
        if (low_link[node] == tour_index[node]) {
            // node is the highest node in an SCC, which includes everything on the stack up to it.
            components.emplace_back();
            vector<int> &component = components.back();
            int x;
 
            do {
                assert(S > 0);
                x = stack[--S];
                in_stack[x] = false;
                which_component[x] = (int) components.size() - 1;
                component.push_back(x);
            } while (x != node);
        }
    }
 
    void build() {
        tour_index.assign(V, -1);
        low_link.assign(V, -1);
        which_component.assign(V, -1);
 
        S = 0;
        stack.resize(V);
        in_stack.assign(V, false);
        tour = 0;
 
        // Note that Tarjan's algorithm provides the SCCs in reverse topological order.
        components = {};
 
        for (int i = 0; i < V; i++)
            if (tour_index[i] < 0)
                dfs(i);
    }
};
 
 
void solve_case() {
    int N, M;
    cin >> N >> M;
    SCC scc(N);
 
    for (int i = 0; i < M; i++) {
        int a, b;
        cin >> a >> b;
        a--; b--;
        scc.add_edge(a, b);
    }
 
    scc.build();


    


class dsu 
{
    public:
        std::vector <int> p, r;
        int n;
    dsu(int _n) : n(_n) 
    {
        p.resize(n);
        r.resize(n);
        iota(p.begin(), p.end(), 0);
    }
 
    inline int get(int x) 
    {
        return (x == p[x] ? x : (p[x] = get(p[x])));
    }
 
    inline void unite(int x, int y) 
    {
        x = get(x);
        y = get(y);

        if(r[x] < r[y])
            p[x] = y;

        else if(r[x] > r[y])
            p[y] = x;

        else{
            p[y] = x;
            r[x] += 1;
        }
    }
};




////////////// DSU NEW AND GOOD VERSION

struct node
{
    int par;
    int rank;
};

node br[2000001];
int ar[2000001] ;

int cnt = 0;

int find(int v)
{
    if(br[v].par == -1) return v;

    return (find(br[v].par));
}

void merge(int a , int b)
{
    if(br[a].rank < br[b].rank)
    {
        swap(a , b);
    }

    br[a].rank += br[b].rank;
    br[b].par = a;
}

int get_cnt(int n)
{
    rep(i,n)
    {
        if(br[i+1].par == -1)
        {
            cnt++;
        }
    }

    return cnt;

}


///////////////////// DSU MORE FEATURES 

class dsu{
  public:
  vector<long long> parent;
    dsu(long long n)
    {
      parent=vector<long long>(n,-1);
    }
    long long find_set(long long v)
    { if(parent[v]<0)
      return v;
      return parent[v]=find_set(parent[v]);
    }
    void make_union(long long u,long long v)
    {  if(abs(parent[u])<abs(parent[v]))
        swap(u,v);  //as below we are considering u as more weighted or greater size graph
        parent[u]=parent[u]+parent[v];
        parent[v]=u;
    }
    void merge(ll x,ll y)
    {
        long long u=find_set(x);
        long long v=find_set(y);
        if(u!=v)
         make_union(u,v);
    }
     bool check_cycle(ll x,ll y)
    {
        long long u=find_set(x);
        long long v=find_set(y);
        if(u!=v)
         return false;    //cycle (will not form)/(not present)
        return true;      //cycle (will form)/(present)
    }
    bool CycleDetectionUndirectedDSU(vector<pair<long long,long long>> &edges)
    {
      for(auto i:edges)
      { 
        long long u=find_set(i.first);
        long long v=find_set(i.second);
        if(u==v)
        return true;
        else
        make_union(u,v);
      }
      return false;
    }
};









////////////////////////////////////////
//                  TO FIND A CYCLE IN A GRAPH

vi g[N];
vi parent(N , 0);
vi seen(N , 0);
set<int> cycle;                    /// ONLY DETECTS AND FIND ONE CYCLE IF MANY CYLRE -- TLE


void dfs(int node, int par)
{
    seen[node]++;
    parent[node] = par;
    if (seen[node] == 2)
    {
        cycle.insert(node);
        int root = parent[node];
        while (node != root)
        {
            cycle.insert(root);
            root = parent[root];
        }
    }
    else
    {
        for (auto nb : g[node])
        {
            if (nb != par)
            {
                dfs(nb, node);
            }
        }
    }
}








////////////// MULTI SOURCE BFS

    #include<bits/stdc++.h>
using namespace std;

int main()
{
   vector<int> sources;

   unordered_map<int,bool> vis;
   unordered_map<int,int> dist;
   queue<int> q;

   for(int i = 0;i<sources.size();i++){
       vis[sources[i]] = true;
       dist[sources[i]] = 0;
       q.push(sources[i]);
   }
// then proceed as usual


   while(!q.empty()){
       int p = q.front();
       q.pop();

       for(int i = 0;i< g[p].size();i++){
           if(!vis[g[p][i]]){
               vis[g[p][i]] = true;
               dist[g[p][i]] = dist[p] + 1;
               q.push(g[p][i]);
           }
       }
   }



    //////// CENTROID OF A TREE

    vector<int> Centroid(const vector<vector<int>> &g) {
        int n = g.size();
        vector<int> centroid;
        vector<int> sz(n);
        function<void (int, int)> dfs = [&](int u, int prev) {
                sz[u] = 1;
                bool is_centroid = true;
                for (auto v : g[u]) if (v != prev) {
                        dfs(v, u);
                        sz[u] += sz[v];
                        if (sz[v] > n / 2) is_centroid = false;
                }
                if (n - sz[u] > n / 2) is_centroid = false;
                if (is_centroid) centroid.push_back(u);
        };
        dfs(0, -1);
        return centroid;
}




///////////////////// CYCLES IN DIRECTED GRAPH


vector<int> graph[N];
vector<char> color;
vector<int> parent;
vector<int> visited;
vector<int> cost(N,0);
int cycle_start, cycle_end;
 
bool dfs_directed(int v) 
{
    color[v] = 1;
    for (int u : graph[v]) 
    {
        if (color[u] == 0) 
        {
            parent[u] = v;
            if (dfs_directed(u))
                return true;	
        } 
        else if (color[u] == 1) 
        {
            cycle_end = v;
            cycle_start = u;
            return true;
        }
    }
    color[v] = 2;
    return false;
}
 
void find_cycle_directed(int n) 
{
    color.assign(n, 0);
    parent.assign(n, -1);
    cycle_start = -1;
    cycle_end=-1;
    int ans=0;
    for (int v = 0; v < n; v++) 
    {
        if (color[v] == 0 && dfs_directed(v))
        {
		    vector<int> cycle;
		    cycle.push_back(cycle_start);
		    for (int v = cycle_end; v != cycle_start; v = parent[v])
		        cycle.push_back(v);
		    cycle.push_back(cycle_start);
		    reverse(cycle.begin(), cycle.end());
		    int mn=inf;
		    for(auto x:cycle)
		    {
		    	mn=min(mn,cost[x]);
		    }
		    ans+=mn;
		    cycle_start = -1;
    		cycle_end=-1;
        }
    }
    cout<<ans;
    
}











#include <bits/stdc++.h>
/* Uncomment following line to see Debug code on leetcode */
// #define cerr cout
namespace _DEBUG_UTIL_
{
    using namespace std;
    /* Primitive Datatypes Print */
    void print(const char *x) {}
    void print(bool x) { cerr << (x ? "T" : "F"); }
    void print(char x) { cerr << '\'' << x << '\''; }
    void print(signed short int x) { cerr << x; }
    void print(unsigned short int x) { cerr << x; }
    void print(signed int x) { cerr << x; }
    void print(unsigned int x) { cerr << x; }
    void print(signed long int x) { cerr << x; }
    void print(unsigned long int x) { cerr << x; }
    void print(signed long long int x) { cerr << x; }
    void print(unsigned long long int x) { cerr << x; }
    void print(float x) { cerr << x; }
    void print(double x) { cerr << x; }
    void print(long double x) { cerr << x; }
    void print(string x) { cerr << '\"' << x << '\"'; }
    template <size_t N>
    void print(bitset<N> x) { cerr << x; }
    void print(vector<bool> x)
    {
        /* vector<bool> doesn't work in general iteration template because of rvalue problems */
        int f = 0;
        cerr << '{';
        for (bool i : x)
        {
            cerr << (f++ ? "," : "");
            cerr << (i ? "T" : "F");
        }
        cerr << "}";
    }
    /* Templates Declarations to support nested datatypes */
    template <typename T>
    void print(T x);
    template <typename T>
    void print(vector<vector<T>> mat);
    template <typename T, size_t N>
    void print(T (&arr)[N]);
    template <typename T, size_t N, size_t M>
    void print(T (&mat)[N][M]);
    template <typename F, typename S>
    void print(pair<F, S> x);
    template <typename T>
    void print(priority_queue<T> pq);
    template <typename T>
    void print(priority_queue<T, vector<T>, greater<T>> pq);
    template <typename T>
    void print(stack<T> st);
    template <typename T>
    void print(queue<T> q);
    /* Template Datatypes Definitions */
    template <typename T>
    void print(T x)
    {
        /* This works for every container that supports range-based loop i.e. vector, set, map, dequeue */
        int f = 0;
        cerr << '{';
        for (auto i : x)
            cerr << (f++ ? "," : ""), print(i);
        cerr << "}";
    }
    template <typename T>
    void print(vector<vector<T>> mat)
    {
        /* Specialized for 2D to format every 1D in new line */
        int f = 0;
        cerr << "{\n";
        for (auto i : mat)
            cerr << (f++ ? ",\n" : ""), print(i);
        cerr << "}\n";
    }
    template <typename T, size_t N>
    void print(T (&arr)[N])
    {
        /* Helps in iterating through arrays and prevent decays */
        int f = 0;
        cerr << '{';
        for (auto &i : arr)
            cerr << (f++ ? "," : ""), print(i);
        cerr << "}";
    }
    template <typename T, size_t N, size_t M>
    void print(T (&mat)[N][M])
    {
        /* Helps in iterating through 2D arrays and prevent decays and also print arrays in new line */
        int f = 0;
        cerr << "{\n";
        for (auto &i : mat)
            cerr << (f++ ? ",\n" : ""), print(i);
        cerr << "}\n";
    }
    template <typename F, typename S>
    void print(pair<F, S> x)
    {
        /* Works for pairs and iterating through maps */
        cerr << '(';
        print(x.first);
        cerr << ',';
        print(x.second);
        cerr << ')';
    }
    template <typename T>
    void print(priority_queue<T> pq)
    {
        int f = 0;
        cerr << '{';
        while (!pq.empty())
            cerr << (f++ ? "," : ""), print(pq.top()), pq.pop();
        cerr << "}";
    }
    template <typename T>
    void print(priority_queue<T, vector<T>, greater<T>> pq)
    {
        int f = 0;
        cerr << '{';
        while (!pq.empty())
            cerr << (f++ ? "," : ""), print(pq.top()), pq.pop();
        cerr << "}";
    }
    template <typename T>
    void print(stack<T> st)
    {
        int f = 0;
        cerr << '{';
        while (!st.empty())
            cerr << (f++ ? "," : ""), print(st.top()), st.pop();
        cerr << "}";
    }
    template <typename T>
    void print(queue<T> q)
    {
        int f = 0;
        cerr << '{';
        while (!q.empty())
            cerr << (f++ ? "," : ""), print(q.front()), q.pop();
        cerr << "}";
    }
    /* Printer functions responsible for.... printing beautifully ? */
    template <typename T>
    void printer(const char *name, T &&head)
    {
        /* Base conditions for printer */
        cerr << name << " = ";
        print(head);
        cerr << "]\n";
    }
    template <typename T, typename... V>
    void printer(const char *names, T &&head, V &&...tail)
    {
        /* Using && to capture both lvalues and rvalues */
        int bracket = 0, i = 0;
        while (names[i] != ',' or bracket != 0)
        {
            if (names[i] == '(')
                bracket++;
            else if (names[i] == ')')
                bracket--;
            i++;
        }
        cerr.write(names, i) << " = ";
        print(head);
        cerr << " ||";
        printer(names + i + 1, tail...);
    }
    /* PrinterArr */
    template <typename T>
    void printerArr(const char *name, T arr[], int N)
    {
        cerr << name << " : {";
        for (int i = 0; i < N; i++)
        {
            cerr << (i ? "," : ""), print(arr[i]);
        }
        cerr << "}]\n";
    }
}
/* Before submitting on LeetCode (Not CodeForces), change #ifndef to #ifdef */
#ifndef ONLINE_JUDGE
#define debug(...) std::cerr << __LINE__ << ": [", _DEBUG_UTIL_::printer(#__VA_ARGS__, __VA_ARGS__)
#define debugArr(arr, n) std::cerr << __LINE__ << ": [", _DEBUG_UTIL_::printerArr(#arr, arr, n)
#else
#define debug(...)
#define debugArr(arr, n)
#endif
