#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// MOD controls frequency of splits
#define MOD 30

// graph edge
typedef struct {
    int u, v;
} EDGE;

// graph edges
EDGE *edges;

// graph representation
int **AL, **IM, *OD, *L, *IL;

// colors of folding
int *color, *color_deg, *color_head, *color_prev, *color_next;

// current solution and best solution
int *sol, *bestsol, soltop = 0, bestsoltop = 0;

// connected components splitting
int n, e, *st, *en, numcc = 1;

// available memory
int **mem;


// initializes the memory allocator
void initMem();

// requests an array
int * allocMem();

// frees an array
void freeMem();

// free all memory
void freeAllMem();

// compares edges for sorting
int edge_compare(const void *, const void *);

// frees all allocated memory
void free_all();

// prints best solution
void print_solution();

// reads the input graph
void read_graph();

// allocates and initializes memory
void allocate_memory();

// checks if graph is edgeless
int is_edgeless(int, const int *);

// gets color of degree > k
int get_greater(int cc);

// gets color of degree = 1
int get_pendant(int cc);

// gets color of degree = 2
int get_deg_two(int cc);

// deletes v from neighborhood of u
void del_neighbor(int *, int, int, int);

// removes v from graph
void del_vertex(int, int *, int);

// checks if two colors are adjacent
int is_neighbor(const int *, int, int);

// removes color from graph
void del_color(int, int *, int);

// merges first color into second
void merge_colors(const int *, int, int);

// updates degree of color
void update_col_deg(const int *, int);

// updates degrees of all colors
void update_colors(const int *);

// gets color of max degree
int get_max_deg(int);

// preprocesses the graph
// handles degree > k
// handles degree = 1
// handles degree = 2
int preprocess(int, int *);

// splits graph into connected components
void connected_components(int, int *);

// does the branching on max degree
void branch(int, int *, int);

// solves vertex cover on bipartite graph
void bipartite_matching(int, const int *, const int *);

// finds an augmenting path in the matching
int update_matching(int, const int *, const int *, int *, int *, int);

// marks vertices reachable by an alternating path
void mark_alternating(const int *, const int *, int *, int *, int, int);

// verifies that final solution covers all edges
void verify_solution();


int *toMap, *fromMap;


int main(int argc, char **argv)
{
    int i;
    read_graph();

    // remove self loops
    for (i = 0; i < soltop; i++)
        del_color(0, OD, color[sol[i]]);

    update_colors(OD);

    // remove isolated
    for (i = 0; i < n; i++)
        if (color_deg[i] == 0)
            del_color(0, OD, i);

    branch(0, OD, 0);

    print_solution();

//    verify_solution();

    fflush(stdout);

//    free_all();

    return 0;
}


void verify_solution() {
    int i, j, ed = 0;
    for (i = 0; i < e; i++) {
        for (j = 0; j < bestsoltop; j++)
            if (bestsol[j] == edges[i].u || bestsol[j] == edges[i].v)
                break;
        if (j == bestsoltop)
            ed++;
    }
    printf("VC size %d - %s \n", bestsoltop, (ed == 0) ? "CORRECT" : "WRONG");
    printf("%d edges not covered \n", ed);
}


void bipartite_matching(int cc, const int *deg, const int *col) {
    int *match = allocMem();
    int *alt = allocMem();
    int *vis = allocMem();

    memset(match, -1, n * sizeof(int));

    int result = 0, i, u;
    for (i = st[cc]; i <= en[cc]; i++) {
        u = color[L[i]];
        if (col[u] == 1 || match[u] > 0)
            continue;
        memset(vis, 0, n * sizeof(int));
        if (update_matching(cc, deg, col, vis, match, u))
            result++;
    }

    memset(alt, 0, n * sizeof(int));
    memset(vis, 0, n * sizeof(int));

    for (i = st[cc]; i <= en[cc]; i++) {
        u = color[L[i]];
        if (col[u] == 0 && match[u] == -1)
            mark_alternating(deg, match, vis, alt, u, 0);
    }

    bestsoltop = 0;
    for (i = st[cc]; i <= en[cc]; i++) {
        u = color[L[i]];
        if (col[u] == alt[u]) {
            bestsol[bestsoltop++] = u;
            alt[u] = -1;
        }
    }

    freeMem();
    freeMem();
    freeMem();

}


void mark_alternating(const int *deg, const int *match, int *vis, int *alt, int u, int flag) {
    if (u == -1 || vis[u])
        return;
    alt[u] = 1;
    vis[u] = 1;
    if (flag) { // take a matching edge
        mark_alternating(deg, match, vis, alt, match[u], 0);
    }
    else { // take a non-matching edge
        int j, i, v, w;
        for (w = color_head[u]; w != -1; w = color_next[w]) {
            for (i = 0; i < deg[w]; i++) {
                v = color[AL[w][i]];
                if (v != match[u])
                    mark_alternating(deg, match, vis, alt, match[u], 1);
            }
        }
    }
}


int update_matching(int cc, const int *deg, const int *col, int *vis, int *match, int u) {
    int i, j, v, w;
    for (w = color_head[u]; w != -1; w = color_next[w]) {
        for (i = 0; i < deg[w]; i++) {
            v = color[AL[w][i]];
            if (col[v] == 0 || vis[v])
                continue;
            vis[v] = 1;
            if (match[v] < 0 || update_matching(cc, deg, col, vis, match, match[v])) {
                match[v] = u;
                match[u] = v;
                return 1;
            }
        }
    }
    return 0;
}


void branch(int cc, int *deg, int depth)
{
    if (bestsoltop <= soltop)
        return;

    if (is_edgeless(cc, deg)) {
        bestsoltop = soltop;
        memcpy(bestsol, sol, soltop * sizeof(int));
        return;
    }
  
  	if (bestsoltop <= soltop + 1)
        return;

    int i, j;
    int d, u, v, w, x;
    int *temp_deg, temp_st, temp_en, temp_numcc;
    int *temp_color, *temp_color_head, *temp_color_prev, *temp_color_next, *temp_color_deg;
    int temp_soltop, temp_bestsoltop;


    while ((w = preprocess(cc, deg)) != -1)
    {
        if (bestsoltop <= soltop)
            return;

        u = v = -1;
        for (x = color_head[w]; x != -1; x = color_next[x]) {
            for (j = 0; j < deg[x]; j++) {
                if (u == -1) {
                    u = color[AL[x][j]];
                } else if (u != color[AL[x][j]]) {
                    v = color[AL[x][j]];
                    break;
                }
            }
            if (u != -1 && v != -1)
                break;
        }

        if (is_neighbor(deg, v, u)) {
            sol[soltop++] = u;
            sol[soltop++] = v;
            del_color(cc, deg, u);
            del_color(cc, deg, v);

        }
        else {
            temp_soltop = soltop;
            temp_bestsoltop = bestsoltop;

            sol[soltop++] = w;
            del_color(cc, deg, w);
            merge_colors(deg, v, u);

            branch(cc, deg, depth);

            if (bestsoltop < temp_bestsoltop) {
                for (i = bestsoltop-1; i >= temp_soltop; i--) {
                    if (bestsol[i] == u) {
                        u = -1;
                    } else if (bestsol[i] == w && u == -1) {
                        bestsol[i] = v;
                        break;
                    }
                }
            }
            return;
        }
    }

    if (bestsoltop <= soltop)
        return;

    if (is_edgeless(cc, deg)) {
        bestsoltop = soltop;
        memcpy(bestsol, sol, soltop * sizeof(int));
        return;
    }
  
  	if (bestsoltop <= soltop + 1)
        return;

    if (en[cc] - st[cc] + 1 > 20 && depth % MOD == 0) {
        connected_components(cc, deg);
        return;
    }

    w = get_max_deg(cc);
    if(w < 0)
        return;

    d = color_deg[w];

    temp_deg = allocMem();
    temp_color = allocMem();
    temp_color_head = allocMem();
    temp_color_prev = allocMem();
    temp_color_next = allocMem();
    temp_color_deg = allocMem();

    for(i = 0; i < n; i++) {
        temp_deg[L[i]] = deg[L[i]];
        temp_color[L[i]] = color[L[i]];
        temp_color_head[i] = color_head[i];
        temp_color_prev[L[i]] = color_prev[L[i]];
        temp_color_next[L[i]] = color_next[L[i]];
        temp_color_deg[i] = color_deg[i];
    }
    temp_st = st[cc];
    temp_en = en[cc];
    temp_numcc = numcc;
    temp_soltop = soltop;

    sol[soltop++] = w;
    del_color(cc, deg, w);

    branch(cc, deg, depth+1);

    for(i = 0; i < n; i++) {
        deg[L[i]] = temp_deg[L[i]];
        color[L[i]] = temp_color[L[i]];
        color_head[i] = temp_color_head[i];
        color_prev[L[i]] = temp_color_prev[L[i]];
        color_next[L[i]] = temp_color_next[L[i]];
        color_deg[i] = temp_color_deg[i];
    }
    st[cc] = temp_st;
    en[cc] = temp_en;
    numcc = temp_numcc;
    soltop = temp_soltop;

    freeMem();
    freeMem();
    freeMem();
    freeMem();
    freeMem();
    freeMem();

    if (soltop + d >= bestsoltop)
        return;

    int *vis = allocMem();
    memset(vis, 0, n * sizeof(int));

    for (u = color_head[w]; u != -1; u = color_next[u])
        for (j = 0; j < deg[u]; j++)
            vis[color[AL[u][j]]] = 1;

    for (i = 0; i < n; i++)
        if (vis[i]) {
            sol[soltop++] = i;
            del_color(cc, deg, i);
        }
    del_color(cc, deg, w);
    freeMem();

    branch(cc, deg, depth+1);

}


void connected_components(int cc, int *deg) {
    int i, j;
    int *temp_sol = allocMem();
    int *temp_bestsol = allocMem();
    memcpy(temp_sol, sol, soltop * sizeof(int));
    memcpy(temp_bestsol, bestsol, bestsoltop * sizeof(int));
    int temp_soltop = soltop;
    int temp_bestsoltop = bestsoltop;

    int *col = allocMem();
    memset(col, -1, n * sizeof(int));
    int *vis = allocMem();
    memset(vis, 0, n * sizeof(int));
    int isBipartite = 1;
    bestsoltop = 0;

    int u, v, w, idx_u, idx_v, idx_w, end = st[cc], lim = en[cc];
    for(idx_u = st[cc]; idx_u <= lim; idx_u++) {
        if(idx_u > end) {
            en[cc] = end;
            soltop = 0;

            if (is_edgeless(cc, deg))
                bestsoltop = 0;
            else if (isBipartite)
                bipartite_matching(cc, deg, col);
            else
                branch(cc, deg, 1);

            memcpy(temp_sol + temp_soltop, bestsol, bestsoltop * sizeof(int));
            temp_soltop += bestsoltop;

            cc = numcc++;
            st[cc] = idx_u;
            end = idx_u;
            isBipartite = 1;
            bestsoltop = 0;
        }
        u = L[idx_u];

        if (col[color[u]] == -1)
            col[color[u]] = 0;

        for (v = color_head[color[u]]; v != -1; v = color_next[v]) {
            idx_v = IL[v];

            if (idx_v <= end)
                continue;

            idx_w = end + 1;
            w = L[idx_w];

            L[idx_v] = w;
            L[idx_w] = v;
            IL[w] = idx_v;
            IL[v] = idx_w;
            end++;
        }
        for(j = 0; j < deg[u]; j++) {
            v = AL[u][j];
            idx_v = IL[v];

            if (col[color[v]] == -1)
                col[color[v]] = 1 - col[color[u]];
            else if (col[color[v]] == col[color[u]])
                isBipartite = 0;

            if (!vis[color[u]] && !vis[color[v]]) {
                bestsol[bestsoltop++] = color[u];
                vis[color[u]] = 1;
                bestsol[bestsoltop++] = color[v];
                vis[color[v]] = 1;
            }

            if (idx_v <= end)
                continue;

            idx_w = end+1;
            w = L[idx_w];

            L[idx_v] = w;
            L[idx_w] = v;
            IL[w] = idx_v;
            IL[v] = idx_w;
            end++;
        }
    }
    freeMem();
    en[cc] = end;
    soltop = 0;

    if (is_edgeless(cc, deg))
        bestsoltop = 0;
    else if (isBipartite)
        bipartite_matching(cc, deg, col);
    else
        branch(cc, deg, 1);

    memcpy(temp_sol + temp_soltop, bestsol, bestsoltop * sizeof(int));
    temp_soltop += bestsoltop;

    soltop = temp_soltop;
    bestsoltop = temp_bestsoltop;
    memcpy(sol, temp_sol, soltop * sizeof(int));
    memcpy(bestsol, temp_bestsol, bestsoltop * sizeof(int));

    if (soltop < bestsoltop) {
        bestsoltop = soltop;
        memcpy(bestsol, sol, soltop * sizeof(int));
    }

    freeMem();
    freeMem();
    freeMem();

}

int three_clique (int cc, int *deg)
{
    int i, j, u, v, a, b, c;
    for (i = 0; i < n; i++) {
        if (color_head[i] != -1 || IL[color_head[i]] < st[cc] || IL[color_head[i]] > en[cc])
            continue;
        if (color_deg[i] != 3)
            continue;
        v = i;
        a = b = c = -1;
        for (u = color_head[v]; u != -1; u = color_next[u]) {
            for (j = 0; j < deg[u]; j++) {
                if (a == -1) {
                    a = color[AL[u][j]];
                }
                else if (a != color[AL[u][j]]) {
                    if (b == -1) {
                        b = color[AL[u][j]];
                        if (!is_neighbor(deg, b, a)) {
                            c = -3;
                            break;
                        }
                    }
                    else if (b != color[AL[u][j]]) {
                        c = color[AL[u][j]];
                        if (!is_neighbor(deg, c, a) || !is_neighbor(deg, c, b)) {
                            c = -3;
                        }
                        break;
                    }
                }
            }
            if (c != -1)
                break;
        }
        if (c != -3) {
            sol[soltop++] = a;
            sol[soltop++] = b;
            sol[soltop++] = c;
            del_color(cc, deg, a);
            del_color(cc, deg, b);
            del_color(cc, deg, c);
            del_color(cc, deg, v);
            return 1;
        }
    }
    return 0;
}


int preprocess(int cc, int *deg)
{
    int greater, pendant, neighbor, degtwo, u, count;

    update_colors(deg);

    while(bestsoltop > soltop) {
        count = 0;

        while ((greater = get_greater(cc)) > -1) {
            count++;
            sol[soltop++] = greater;
            del_color(cc, deg, greater);
            if (bestsoltop <= soltop)
                return -1;
            update_colors(deg);
        }

        while ((pendant = get_pendant(cc)) > -1) {
            count++;
            neighbor = pendant;
            for (u = color_head[pendant]; u != -1; u = color_next[u]) {
                if (deg[u] > 0) {
                    neighbor = color[AL[u][0]];
                    break;
                }
            }
            sol[soltop++] = neighbor;
            del_color(cc, deg, neighbor);
            del_color(cc, deg, pendant);
            if (bestsoltop <= soltop)
                return -1;
            update_colors(deg);
        }

        if (en[cc] - st[cc] + 1 > 20 && (degtwo = get_deg_two(cc)) > -1)
            return degtwo;

        while (en[cc] - st[cc] + 1 > 20 && bestsoltop - soltop - 1 >= 3 && three_clique(cc, deg)) {
            if (bestsoltop <= soltop)
                return -1;
            update_colors(deg);
        }

        if (count == 0)
            return -1;
    }
    return -1;
}


int get_max_deg(int cc)
{
    int kmax = 0, maxdeg = 0, idx = -1, ne = 0, nv = 0, count = 0, deg, i, j;
    int k = bestsoltop - soltop - 1;
    int *degreeIdx = allocMem();
    memset(degreeIdx, 0, n * sizeof(int));

    for (i = 0; i < n; i++) {
        if (color_head[i] == -1 || IL[color_head[i]] < st[cc] || IL[color_head[i]] > en[cc])
            continue;
        deg = color_deg[i];
        if (deg > maxdeg) {
            maxdeg = deg;
            idx = i;
        }
        degreeIdx[deg]++;
        if (deg > 0)
            nv++;
        ne += deg;
    }

    for(i = maxdeg; i > 0; i--) {
        if(count >= k)
            break;

        if(count + degreeIdx[i] > k) {
            kmax += i * (k - count);
            break;
        }
        else
        {
            kmax += i * degreeIdx[i];
            count += degreeIdx[i];
        }
    }
    freeMem();
    ne /= 2;

    if(kmax < ne)
        return -1;

    if(en[cc] - st[cc] + 1 > 20 && nv > k * (1 + maxdeg/3))
        return -1;
  	if (nv > k * (1 + maxdeg/2))
  		return -1;

    return idx;
}


void update_colors(const int *deg) {
    int i;
    for (i = 0; i < n; i++)
        if (color_deg[i] < 0)
            update_col_deg(deg, i);
}


void update_col_deg(const int *deg, int col) {
    int *vis = allocMem();
    memset(vis, 0, n * sizeof(int));

    color_deg[col] = 0;
    int i, j, u, v;
    for (u = color_head[col]; u != -1; u = color_next[u]) {
        for (j = 0; j < deg[u]; j++) {
            v = AL[u][j];
            if (++vis[color[v]] == 1)
                color_deg[col]++;
        }
    }
    freeMem();
}


void merge_colors(const int *deg, int colA, int colB) {
    int u, v, w, i;
    for (u = color_head[colA]; u != -1; u = w) {
        w = color_next[u];

        for (i = 0; i < deg[u]; i++)
            color_deg[color[AL[u][i]]] = -1;

        v = color_head[colB];
        if (v != -1)
            color_prev[v] = u;
        color_prev[u] = -1;
        color_next[u] = v;
        color_head[colB] = u;

        color[u] = colB;
    }
    color_deg[colA] = 0;
    color_head[colA] = -1;
    color_deg[colB] = -1;
}


void del_color(int cc, int *deg, int col) {
    int u;
    while ((u = color_head[col]) != -1)
        del_vertex(cc, deg, u);
    color_deg[col] = 0;
    color_head[col] = -1;
}


int is_neighbor(const int *deg, int colA, int colB) {
    int i, u;
    for (u = color_head[colA]; u != -1; u = color_next[u])
        for (i = 0; i < deg[u]; i++)
            if (color[AL[u][i]] == colB)
                return 1;
    return 0;
}


void del_vertex(int cc, int *deg, int v)
{
    int u = L[en[cc]], idx_v = IL[v], idx_u = en[cc]--, i;
    L[idx_v] = u;
    IL[u] = idx_v;
    L[idx_u] = v;
    IL[v] = idx_u;

    for(i = deg[v]-1; i >= 0; i--) {
        u = AL[v][i];
        del_neighbor(deg, u, v, IM[v][i]);
    }
    deg[v] = 0;

    int prev = color_prev[v];
    int next = color_next[v];
    if (prev == -1 && next == -1) { // only element
        color_head[color[v]] = -1;
    }
    else if (prev == -1) { // first element
        color_head[color[v]] = next;
        color_prev[next] = -1;
    }
    else if (next == -1) { // last element
        color_next[prev] = -1;
    }
    else {
        color_next[prev] = next;
        color_prev[next] = prev;
    }
    color_prev[v] = color_next[v] = -1;
}


void del_neighbor(int *deg, int u, int v, int idx_v)
{
    int w, idx_w, temp;
    deg[u]--;
    idx_w = deg[u];
    w = AL[u][idx_w];
    AL[u][idx_w] = v;
    AL[u][idx_v] = w;
    IM[v][IM[u][idx_v]] = idx_w;
    IM[w][IM[u][idx_w]] = idx_v;
    temp = IM[u][idx_v];
    IM[u][idx_v] = IM[u][idx_w];
    IM[u][idx_w] = temp;

    color_deg[color[u]] = color_deg[color[v]] = -1;
}


int get_deg_two(int cc)
{
    int i;
    for (i = st[cc]; i <= en[cc]; i++)
        if (color_deg[color[L[i]]] == 2)
            return color[L[i]];
    return -1;
}


int get_pendant(int cc)
{
    int i;
    for (i = st[cc]; i <= en[cc]; i++)
        if (color_deg[color[L[i]]] == 1)
            return color[L[i]];
    return -1;
}


int get_greater(int cc)
{
    int i, k = bestsoltop - soltop - 1;
    for (i = st[cc]; i <= en[cc]; i++)
        if (color_deg[color[L[i]]] > k)
            return color[L[i]];
    return -1;
}


int is_edgeless(int cc, const int *deg)
{
    int i;
    for(i = st[cc]; i <= en[cc]; i++)
        if(deg[L[i]] > 0)
            return 0;
    return 1;
}


void allocate_memory()
{
    int i, u, v;

    AL = (int **) malloc(n * sizeof(int *));
    IM = (int **) malloc(n * sizeof(int *));
    L = (int *) malloc(n * sizeof(int));
    IL = (int *) malloc(n * sizeof(int));
    color = (int *) malloc(n * sizeof(int));
    color_deg = (int *) malloc(n * sizeof(int));
    color_head = (int *) malloc(n * sizeof(int));
    color_prev = (int *) malloc(n * sizeof(int));
    color_next = (int *) malloc(n * sizeof(int));
    st = (int *) malloc(n * sizeof(int));
    en = (int *) malloc(n * sizeof(int));
    bestsol = (int *) malloc(n * sizeof(int));
    sol = (int *) malloc(n * sizeof(int));
    soltop = 0;

    initMem();

    for (i = 0; i < n; i++) {
        AL[i] = (int *) malloc(OD[i] * sizeof(int));
        IM[i] = (int *) malloc(OD[i] * sizeof(int));
        memset(IM[i], -1, OD[i] * sizeof(int));
        L[i] = i;
        IL[i] = i;
        color[i] = i;
        color_head[i] = i;
        color_prev[i] = -1;
        color_next[i] = -1;
        color_deg[i] = OD[i];
        OD[i] = 0;
    }

    int *vis = allocMem();
    memset(vis, 0, n * sizeof(int));
    bestsoltop = 0;

    for (i = 0; i < e; i++) {
        if (i > 0 && edges[i].u == edges[i-1].u && edges[i].v == edges[i-1].v)
            continue; // skip all duplicate edges
        u = edges[i].u, v = edges[i].v;
        if (u == v && !vis[u]) { // self loop
            sol[soltop++] = u;
            bestsol[bestsoltop++] = u;
            vis[u] = 1;
        }
        else {
            AL[u][OD[u]] = v;
            AL[v][OD[v]] = u;
            IM[u][OD[u]] = OD[v];
            IM[v][OD[v]] = OD[u];
            OD[u]++, OD[v]++;
            if (!vis[u] && !vis[v]) {
                bestsol[bestsoltop++] = u;
                vis[u] = 1;
                bestsol[bestsoltop++] = v;
                vis[v] = 1;
            }
        }
    }
    freeMem();

    numcc = 1;
    st[0] = 0;
    en[0] = n-1;
}


void read_graph()
{
    int i, j, u, v;

    while (!scanf("p td %d %d", &n, &e))
        scanf("%*[^\n]\n", NULL);

    toMap = (int *) malloc(n * sizeof(int));
    fromMap = (int *) malloc(n * sizeof(int));

    for (i = 0; i < n; i++)
        toMap[i] = i;

    srand(time(NULL));
    for (i = 1; i < n; i++) {
        j = (int) (((long double) rand() / (long double) RAND_MAX) * n);
        u = toMap[i];
        toMap[i] = toMap[j];
        toMap[j] = u;
        fromMap[toMap[i]] = i;
        fromMap[toMap[j]] = j;
    }

    edges = (EDGE *) malloc(e * sizeof(EDGE));

    for (i = 0; i < e; i++) {
        while (!scanf("%d %d", &u, &v))
            scanf("%*[^\n]\n", NULL);
        u--; v--;
        u = toMap[u];
        v = toMap[v];
        edges[i].u = (u < v) ? u : v;
        edges[i].v = (u < v) ? v : u;
    }

    qsort(edges, e, sizeof(EDGE), edge_compare);

    OD = (int *) malloc(n * sizeof(int));
    memset(OD, 0, n * sizeof(int));

    for (i = 0; i < e; i++) {
        if (i > 0 && edges[i].u == edges[i-1].u && edges[i].v == edges[i-1].v)
            continue; // skip all duplicate edges
        if (edges[i].u != edges[i].v) { // avoid self loop
            OD[edges[i].u]++;
            OD[edges[i].v]++;
        }
    }

    allocate_memory();

}


void print_solution()
{
    int i;
    printf("s vc %d %d\n", n, bestsoltop);
    for(i = 0; i < bestsoltop; i++)
        printf("%d\n", fromMap[bestsol[i]] + 1);
    free(toMap);
    free(fromMap);
}


void free_all()
{
    int i;
    for(i=0;i<n;i++) {
        free(AL[i]);
        free(IM[i]);
    }
    free(AL);
    free(IM);
    free(OD);
    free(L);
    free(IL);
    free(st);
    free(en);
    free(sol);
    free(bestsol);
    free(color);
    free(color_deg);
    free(color_head);
    free(color_prev);
    free(color_next);
    free(edges);
    freeAllMem();
}


int edge_compare(const void *s1, const void *s2)
{
    EDGE *e1 = (EDGE *) s1;
    EDGE *e2 = (EDGE *) s2;
    if (e1->u == e2->u)
        return e1->v - e2->v;
    return e1->u - e2->u;
}


int memIdx, memSz, memMx;

void initMem()
{
    memIdx = 0;
    memSz = 0;
    memMx = 100000;
    mem = (int **) malloc(memMx * sizeof(int *));
}

int * allocMem()
{
    if (memIdx >= memMx) {
        memMx *= 2;
        mem = (int **) realloc(mem, memMx * sizeof(int *));
    }
    if (memIdx >= memSz) {
        mem[memSz++] = (int *) malloc(n * sizeof(int));
    }
    return mem[memIdx++];
}

void freeMem()
{
    memIdx--;
}

void freeAllMem()
{
    while (--memSz >= 0) {
        free(mem[memSz]);
    }
    free(mem);
}