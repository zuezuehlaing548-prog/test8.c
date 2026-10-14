/*
 * 과제 08: 최소 비용 신장 트리 알고리즘 비교
 * - 인접 리스트 + Kruskal
 * - 인접 행렬 + Prim
 * - 희소 그래프(E=100), 밀집 그래프(E=600), 정점 50개
 *
 * 컴파일: gcc mst.c -o mst
 * 실행  : ./mst          (실행할 때마다 다른 그래프)
 *         ./mst 1234     (seed를 정하면 같은 그래프)
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define N 50          /* 정점 수 */
#define SPARSE_E 100  /* 희소 그래프 간선 수 */
#define DENSE_E 600   /* 밀집 그래프 간선 수 */
#define MAX_W 100     /* 가중치 범위: 1 ~ 100 */
#define REPEAT 1000   /* 시간이 너무 짧아서 REPEAT번 반복한 평균을 사용 */
#define INF 1000000000

typedef struct {
    int u, v, w;
} Edge;

typedef struct Node {
    int v, w;
    struct Node *next;
} Node;

/* ---------------------------------------------------------
 * 1. 그래프 생성
 * --------------------------------------------------------- */

/* 연결 그래프인지 확인 (BFS) */
int is_connected(Edge *edges, int E)
{
    int adj[N][N] = {0};
    int visited[N] = {0};
    int queue[N], front = 0, rear = 0, count = 0;
    int i;

    for (i = 0; i < E; i++) {
        adj[edges[i].u][edges[i].v] = 1;
        adj[edges[i].v][edges[i].u] = 1;
    }

    visited[0] = 1;
    queue[rear++] = 0;
    while (front < rear) {
        int cur = queue[front++];
        count++;
        for (i = 0; i < N; i++) {
            if (adj[cur][i] && !visited[i]) {
                visited[i] = 1;
                queue[rear++] = i;
            }
        }
    }
    return count == N;
}

/* 랜덤 연결 그래프 생성
 * 1) 정점 i를 이전 정점 j(< i) 중 하나에 연결 -> 신장 트리가 먼저 만들어짐 (연결 보장)
 * 2) 남은 간선은 중복/자기 자신 연결을 피해서 랜덤으로 추가 */
void generate_graph(Edge *edges, int E)
{
    int exists[N][N] = {0};
    int cnt = 0, i;

    for (i = 1; i < N; i++) {
        int j = rand() % i;
        edges[cnt].u = j;
        edges[cnt].v = i;
        edges[cnt].w = rand() % MAX_W + 1;
        exists[i][j] = exists[j][i] = 1;
        cnt++;
    }

    while (cnt < E) {
        int u = rand() % N;
        int v = rand() % N;
        if (u == v || exists[u][v])
            continue;
        edges[cnt].u = u;
        edges[cnt].v = v;
        edges[cnt].w = rand() % MAX_W + 1;
        exists[u][v] = exists[v][u] = 1;
        cnt++;
    }
}

/* ---------------------------------------------------------
 * 2. 그래프 표현
 * --------------------------------------------------------- */

/* 인접 리스트 만들기 (무방향이라서 노드 2개씩 추가) */
Node **build_list(Edge *edges, int E, size_t *mem)
{
    Node **head = (Node **)calloc(N, sizeof(Node *));
    int i;

    for (i = 0; i < E; i++) {
        Node *a = (Node *)malloc(sizeof(Node));
        Node *b = (Node *)malloc(sizeof(Node));

        a->v = edges[i].v;
        a->w = edges[i].w;
        a->next = head[edges[i].u];
        head[edges[i].u] = a;

        b->v = edges[i].u;
        b->w = edges[i].w;
        b->next = head[edges[i].v];
        head[edges[i].v] = b;
    }
    /* 메모리 = head 배열 + 노드 (2 * E개) */
    *mem = sizeof(Node *) * N + sizeof(Node) * 2 * E;
    return head;
}

void free_list(Node **head)
{
    int i;
    for (i = 0; i < N; i++) {
        Node *cur = head[i];
        while (cur) {
            Node *tmp = cur;
            cur = cur->next;
            free(tmp);
        }
    }
    free(head);
}

/* 인접 행렬 만들기 (0이면 간선 없음, 가중치는 양수라서 괜찮음) */
void build_matrix(int m[N][N], Edge *edges, int E)
{
    int i, j;
    for (i = 0; i < N; i++)
        for (j = 0; j < N; j++)
            m[i][j] = 0;
    for (i = 0; i < E; i++) {
        m[edges[i].u][edges[i].v] = edges[i].w;
        m[edges[i].v][edges[i].u] = edges[i].w;
    }
}

/* ---------------------------------------------------------
 * 3. Kruskal (인접 리스트 + Union-Find)
 * --------------------------------------------------------- */

int cmp_edge(const void *a, const void *b)
{
    return ((const Edge *)a)->w - ((const Edge *)b)->w;
}

int find(int *parent, int x)
{
    if (parent[x] != x)
        parent[x] = find(parent, parent[x]); /* 경로 압축 */
    return parent[x];
}

/* union이 성공하면 1, 이미 같은 집합이면 0 (사이클) */
int union_set(int *parent, int *rank, int a, int b)
{
    int ra = find(parent, a);
    int rb = find(parent, b);

    if (ra == rb)
        return 0;
    if (rank[ra] < rank[rb]) {
        parent[ra] = rb;
    } else if (rank[ra] > rank[rb]) {
        parent[rb] = ra;
    } else {
        parent[rb] = ra;
        rank[ra]++;
    }
    return 1;
}

/* 리턴: MST 전체 비용, mst[]에 선택된 간선 저장, *cnt에 간선 수 저장 */
int kruskal(Node **head, int E, Edge *mst, int *cnt)
{
    Edge *list = (Edge *)malloc(sizeof(Edge) * E);
    int parent[N], rank[N];
    int i, k = 0, total = 0;
    Node *cur;

    /* 인접 리스트에서 간선 꺼내기 (u < v 인 것만, 중복 방지) */
    for (i = 0; i < N; i++) {
        for (cur = head[i]; cur; cur = cur->next) {
            if (i < cur->v) {
                list[k].u = i;
                list[k].v = cur->v;
                list[k].w = cur->w;
                k++;
            }
        }
    }

    /* 가중치 순으로 정렬 */
    qsort(list, k, sizeof(Edge), cmp_edge);

    /* Union-Find 초기화 */
    for (i = 0; i < N; i++) {
        parent[i] = i;
        rank[i] = 0;
    }

    *cnt = 0;
    for (i = 0; i < k && *cnt < N - 1; i++) {
        if (union_set(parent, rank, list[i].u, list[i].v)) {
            mst[*cnt] = list[i];
            (*cnt)++;
            total += list[i].w;
        }
    }

    free(list);
    return total;
}

/* Kruskal이 쓰는 메모리: 인접 리스트 + 간선 배열 + Union-Find(parent, rank) + MST 결과 배열 */
size_t kruskal_memory(size_t list_mem, int E)
{
    return list_mem
         + sizeof(Edge) * E
         + sizeof(int) * N * 2
         + sizeof(Edge) * (N - 1);
}

/* 
 * 4. Prim (인접 행렬)
 */

int prim(int m[N][N], Edge *mst, int *cnt)
{
    int key[N], from[N], visited[N];
    int i, j, total = 0;

    for (i = 0; i < N; i++) {
        key[i] = INF;
        from[i] = -1;
        visited[i] = 0;
    }
    key[0] = 0; /* 시작 정점 0 */
    *cnt = 0;

    for (i = 0; i < N; i++) {
        /* 방문 안 한 정점 중 key가 가장 작은 정점 고르기 */
        int u = -1, min = INF;
        for (j = 0; j < N; j++) {
            if (!visited[j] && key[j] < min) {
                min = key[j];
                u = j;
            }
        }
        if (u == -1)
            break;

        visited[u] = 1;
        if (from[u] != -1) {
            mst[*cnt].u = from[u];
            mst[*cnt].v = u;
            mst[*cnt].w = key[u];
            (*cnt)++;
            total += key[u];
        }

        /* u와 연결된 정점의 key 갱신 */
        for (j = 0; j < N; j++) {
            if (m[u][j] > 0 && !visited[j] && m[u][j] < key[j]) {
                key[j] = m[u][j];
                from[j] = u;
            }
        }
    }
    return total;
}

/* Prim이 쓰는 메모리: 인접 행렬 + key, from, visited 배열 + MST 결과 배열 */
size_t prim_memory(void)
{
    return sizeof(int) * N * N
         + sizeof(int) * N * 3
         + sizeof(Edge) * (N - 1);
}

/* 
 * 5. 시간 측정, 출력
 */

double now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

void print_result(const char *title, int E, int cnt, int cost, size_t mem, double ms)
{
    printf("%s\n", title);
    printf("Vertices      : %d\n", N);
    printf("Edges         : %d\n", E);
    printf("MST Edges     : %d\n", cnt);
    printf("MST Cost      : %d\n", cost);
    printf("Memory        : %zu Bytes\n", mem);
    printf("Execution Time: %.6f ms\n\n", ms);
}

void print_mst(const char *title, Edge *mst, int cnt)
{
    int i;
    printf("[%s] MST 간선 목록\n", title);
    for (i = 0; i < cnt; i++)
        printf("  (%2d - %2d) w=%d\n", mst[i].u, mst[i].v, mst[i].w);
    printf("\n");
}

/* Kruskal을 REPEAT번 돌려서 평균 시간(ms) 구하기 */
double run_kruskal(Node **head, int E, Edge *mst, int *cnt, int *cost)
{
    double start, end;
    int r;

    start = now_ms();
    for (r = 0; r < REPEAT; r++)
        *cost = kruskal(head, E, mst, cnt);
    end = now_ms();
    return (end - start) / REPEAT;
}

/* Prim을 REPEAT번 돌려서 평균 시간(ms) 구하기 */
double run_prim(int m[N][N], Edge *mst, int *cnt, int *cost)
{
    double start, end;
    int r;

    start = now_ms();
    for (r = 0; r < REPEAT; r++)
        *cost = prim(m, mst, cnt);
    end = now_ms();
    return (end - start) / REPEAT;
}


static int mat_sparse[N][N];
static int mat_dense[N][N];

int main(int argc, char *argv[])
{
    Edge sparse_edges[SPARSE_E];
    Edge dense_edges[DENSE_E];
    Edge mst[N - 1];
    Node **list_sparse, **list_dense;
    size_t list_mem_sparse, list_mem_dense;
    int cnt, cost[4];
    double ms;
    unsigned int seed = (argc > 1) ? (unsigned int)atoi(argv[1]) : (unsigned int)time(NULL);

    srand(seed);
    printf("seed = %u\n\n", seed);

    /* 연결 그래프가 나올 때까지 생성 (확인용) */
    do {
        generate_graph(sparse_edges, SPARSE_E);
    } while (!is_connected(sparse_edges, SPARSE_E));
    do {
        generate_graph(dense_edges, DENSE_E);
    } while (!is_connected(dense_edges, DENSE_E));

    /* 같은 그래프를 리스트와 행렬로 각각 표현 */
    list_sparse = build_list(sparse_edges, SPARSE_E, &list_mem_sparse);
    list_dense = build_list(dense_edges, DENSE_E, &list_mem_dense);
    build_matrix(mat_sparse, sparse_edges, SPARSE_E);
    build_matrix(mat_dense, dense_edges, DENSE_E);

    /* Case 1 : Sparse - 인접 리스트 - Kruskal */
    ms = run_kruskal(list_sparse, SPARSE_E, mst, &cnt, &cost[0]);
    print_result("Case 1 : Sparse Graph - Adjacency List - Kruskal",
                 SPARSE_E, cnt, cost[0], kruskal_memory(list_mem_sparse, SPARSE_E), ms);
    print_mst("Case 1", mst, cnt);

    /* Case 2 : Dense - 인접 리스트 - Kruskal */
    ms = run_kruskal(list_dense, DENSE_E, mst, &cnt, &cost[1]);
    print_result("Case 2 : Dense Graph - Adjacency List - Kruskal",
                 DENSE_E, cnt, cost[1], kruskal_memory(list_mem_dense, DENSE_E), ms);
    print_mst("Case 2", mst, cnt);

    /* Case 3 : Sparse - 인접 행렬 - Prim */
    ms = run_prim(mat_sparse, mst, &cnt, &cost[2]);
    print_result("Case 3 : Sparse Graph - Adjacency Matrix - Prim",
                 SPARSE_E, cnt, cost[2], prim_memory(), ms);
    print_mst("Case 3", mst, cnt);

    /* Case 4 : Dense - 인접 행렬 - Prim */
    ms = run_prim(mat_dense, mst, &cnt, &cost[3]);
    print_result("Case 4 : Dense Graph - Adjacency Matrix - Prim",
                 DENSE_E, cnt, cost[3], prim_memory(), ms);
    print_mst("Case 4", mst, cnt);

    /* Kruskal과 Prim의 MST 비용이 같은지 확인 */
    printf("Sparse: Kruskal = %d, Prim = %d -> %s\n", cost[0], cost[2],
           cost[0] == cost[2] ? "같음 (OK)" : "다름 (ERROR)");
    printf("Dense : Kruskal = %d, Prim = %d -> %s\n", cost[1], cost[3],
           cost[1] == cost[3] ? "같음 (OK)" : "다름 (ERROR)");
    printf("\n※ 실행시간은 알고리즘을 %d번 반복한 평균값입니다.\n", REPEAT);

    free_list(list_sparse);
    free_list(list_dense);
    return 0;
}
