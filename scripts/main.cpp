#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>
#include <chrono>

using namespace std;

constexpr int MAXN = 256;

// Exact integer floor((p * d - 1) / q) for q > 0
inline long long floor_strict_lt(long long p, long long d, long long q) {
    long long num = p * d - 1;
    if (num >= 0) return num / q;
    return -((-num + q - 1) / q);
}

// Exact integer ceil((p * d) / q) for q > 0
inline long long ceil_ge(long long p, long long d, long long q) {
    long long num = p * d;
    if (num >= 0) return (num + q - 1) / q;
    return -((-num) / q);
}

int N;
int target[MAXN];
int seq[MAXN];
int rem_vis[MAXN];
int max_p[MAXN], max_q[MAXN];
bool found = false;
int found_seq[MAXN];
long long nodes = 0;
long long node_limit = 200000000LL; // bumped to 200M
bool aborted = false;

void dfs(int m, bool strictly_less) {
    if (found || aborted) return;
    nodes++;
    if (nodes > node_limit) {
        aborted = true;
        return;
    }
    if (m == N) {
        for (int i = 0; i < N; i++) {
            if (rem_vis[i] != 0) return;
        }
        if (strictly_less) {
            found = true;
            for (int i = 0; i < N; i++) found_seq[i] = seq[i];
        }
        return;
    }

    int UB[MAXN];
    int LB[MAXN];
    for (int j = m; j < N; j++) {
        UB[j] = N - 1;
        if (N == 1) LB[j] = 0;
        else if (j == 0 || j == N - 1) LB[j] = 1;
        else LB[j] = 2;
    }
    if (!strictly_less && UB[m] > target[m]) {
        UB[m] = target[m];
    }

    // Tightening from rem_vis[i] == 0
    for (int i = 0; i < m; i++) {
        if (rem_vis[i] == 0) {
            if (i == m - 1) return; // m-1 always sees m
            long long p = max_p[i], q = max_q[i];
            for (int j = m; j < N; j++) {
                long long ub_j = seq[i] + floor_strict_lt(p, j - i, q);
                if (ub_j < UB[j]) {
                    UB[j] = (int)ub_j;
                    if (UB[j] < LB[j]) return;
                }
            }
        }
    }

    // Fixpoint propagation for rem_vis[i] > 0
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < m; i++) {
            if (rem_vis[i] > 0) {
                if (i == m - 1) {
                    if (rem_vis[i] > N - m) return;
                } else {
                    int can_count = 0;
                    long long p = max_p[i], q = max_q[i];
                    for (int j = m; j < N; j++) {
                        long long need = seq[i] + ceil_ge(p, j - i, q);
                        if (need <= UB[j]) can_count++;
                    }
                    if (can_count < rem_vis[i]) return;
                    if (can_count == rem_vis[i]) {
                        for (int j = m; j < N; j++) {
                            long long need = seq[i] + ceil_ge(p, j - i, q);
                            if (need <= UB[j] && need > LB[j]) {
                                LB[j] = (int)need;
                                if (LB[j] > UB[j]) return;
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }

    // Global remaining edge capacity check
    int rem_sum = 0;
    for (int i = 0; i < m; i++) rem_sum += rem_vis[i];
    int max_absorb = 0;
    for (int j = m; j < N; j++) {
        max_absorb += min(m, UB[j]);
    }
    if (rem_sum > max_absorb) return;

    // Tighten LB[m] and UB[m] based on guaranteed/possible visibilities at position m
    if (m > 0) {
        int min_vis_left = 1; // always sees m-1
        int max_vis_left = 1;
        for (int i = 0; i < m - 1; i++) {
            if (rem_vis[i] == 0) continue;
            long long need = seq[i] + ceil_ge(max_p[i], m - i, max_q[i]);
            if (need <= LB[m]) min_vis_left++;
            if (need <= UB[m]) max_vis_left++;
        }
        int min_vis_right = (m < N - 1) ? 1 : 0;
        int max_vis_right = N - 1 - m;
        if (LB[m] < min_vis_left + min_vis_right) LB[m] = min_vis_left + min_vis_right;
        if (UB[m] > max_vis_left + max_vis_right) UB[m] = max_vis_left + max_vis_right;
        if (LB[m] > UB[m]) return;
    }

    int saved_rem[MAXN], saved_p[MAXN], saved_q[MAXN];
    for (int i = 0; i < m; i++) {
        saved_rem[i] = rem_vis[i];
        saved_p[i] = max_p[i];
        saved_q[i] = max_q[i];
    }

    int min_rem_m = (m < N - 1) ? 1 : 0;
    int max_rem_m = N - 1 - m;

    for (int v = LB[m]; v <= UB[m]; v++) {
        seq[m] = v;
        int vis_left = 0;
        bool ok = true;
        for (int i = 0; i < m; i++) {
            int dy = v - seq[i];
            int dx = m - i;
            bool sees = false;
            if (i == m - 1) {
                sees = true;
                max_p[i] = dy;
                max_q[i] = dx;
            } else {
                if ((long long)dy * saved_q[i] >= (long long)saved_p[i] * dx) {
                    sees = true;
                    max_p[i] = dy;
                    max_q[i] = dx;
                } else {
                    max_p[i] = saved_p[i];
                    max_q[i] = saved_q[i];
                }
            }
            if (sees) {
                vis_left++;
                rem_vis[i] = saved_rem[i] - 1;
                if (rem_vis[i] < 0) {
                    ok = false;
                    break;
                }
            } else {
                rem_vis[i] = saved_rem[i];
            }
        }
        if (ok) {
            int rem_m = v - vis_left;
            if (rem_m >= min_rem_m && rem_m <= max_rem_m) {
                rem_vis[m] = rem_m;
                dfs(m + 1, strictly_less || (v < target[m]));
                if (found || aborted) return;
            }
        }
        for (int i = 0; i < m; i++) {
            rem_vis[i] = saved_rem[i];
            max_p[i] = saved_p[i];
            max_q[i] = saved_q[i];
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string line;
    while (getline(cin, line)) {
        // Strip any trailing "// ..." comment if re-pasting previous output
        size_t comment_pos = line.find("//");
        if (comment_pos != string::npos) line = line.substr(0, comment_pos);

        istringstream iss(line);
        vector<int> row;
        int x;
        while (iss >> x) row.push_back(x);
        if (row.empty()) continue;

        N = (int)row.size();
        if (N >= MAXN) {
            cout << "// ERROR: N=" << N << " exceeds MAXN=" << MAXN << "\n";
            continue;
        }
        for (int i = 0; i < N; i++) target[i] = row[i];

        found = false;
        aborted = false;
        nodes = 0;

        auto t0 = chrono::steady_clock::now();
        dfs(0, false);
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();

        if (found) {
            for (int i = 0; i < N; i++) cout << found_seq[i] << (i + 1 == N ? "" : " ");
            cout << "  // IMPROVED (n=" << N << ", nodes=" << nodes << ", " << ms << "ms)\n";
        } else {
            for (int i = 0; i < N; i++) cout << target[i] << (i + 1 == N ? "" : " ");
            cout << "  // " << (aborted ? "ABORTED" : "OPTIMAL") << " (n=" << N << ", nodes=" << nodes << ", " << ms << "ms)\n";
        }
        cout.flush();
    }
    return 0;
}
