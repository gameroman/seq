#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>
#include <chrono>
#include <cstring>

using namespace std;

constexpr int MAXN = 256;

// Fast 32-bit exact integer floor((p * d - 1) / q) for q > 0 (safe for N <= 4096)
inline int floor_strict_lt(int p, int d, int q) {
    int num = p * d - 1;
    if (num >= 0) return num / q;
    return -((-num + q - 1) / q);
}

// Fast 32-bit exact integer ceil((p * d) / q) for q > 0 (safe for N <= 4096)
inline int ceil_ge(int p, int d, int q) {
    int num = p * d;
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
long long node_limit = 200000000LL;
bool aborted = false;

void dfs(int m, bool strictly_less, const int* parent_UB, const int* just_zero, int jz_cnt) {
    if (found || aborted) return;
    if (++nodes > node_limit) {
        aborted = true;
        return;
    }

    if (m == N) {
        for (int i = 0; i < N; i++) {
            if (rem_vis[i] != 0) return;
        }
        if (strictly_less) {
            found = true;
            memcpy(found_seq, seq, N * sizeof(int));
        }
        return;
    }

    // m-1 always sees m, so rem_vis[m-1] == 0 is immediately impossible
    if (m > 0 && rem_vis[m - 1] == 0) return;

    int UB[MAXN];
    int LB[MAXN];
    if (m == 0) {
        const int default_ub = N - 1;
        for (int j = 0; j < N; j++) UB[j] = default_ub;
    } else {
        memcpy(UB + m, parent_UB + m, (N - m) * sizeof(int));
    }

    for (int j = m; j < N; j++) {
        if (N == 1) LB[j] = 0;
        else if (j == 0 || j == N - 1) LB[j] = 1;
        else LB[j] = 2;
    }
    if (!strictly_less && UB[m] > target[m]) {
        UB[m] = target[m];
    }
    if (LB[m] > UB[m]) return;

    // 1. Tighten UB ONLY for vertices whose rem_vis[i] just hit 0 at step m-1
    for (int k = 0; k < jz_cnt; k++) {
        const int i = just_zero[k];
        const int p = max_p[i], q = max_q[i];
        const int base = seq[i];
        for (int j = m; j < N; j++) {
            int ub_j = base + floor_strict_lt(p, j - i, q);
            if (ub_j < UB[j]) {
                UB[j] = ub_j;
                if (UB[j] < LB[j]) return;
            }
        }
    }

    // 2. Pack need[idx][j] contiguously ONLY for active i (rem_vis[i] > 0)
    static int need[MAXN][MAXN]; // Only rows 0..active_cnt-1 are touched (stays in L1 cache)
    int active_i[MAXN];
    int active_cnt = 0;
    int rem_sum = 0;

    for (int i = 0; i < m; i++) {
        const int rv = rem_vis[i];
        if (rv > 0) {
            rem_sum += rv;
            if (i == m - 1) {
                if (rv > N - m) return;
            } else {
                const int idx = active_cnt++;
                active_i[idx] = i;
                const int p = max_p[i], q = max_q[i];
                const int base = seq[i];
                for (int j = m; j < N; j++) {
                    int nd = base + ceil_ge(p, j - i, q);
                    need[idx][j] = (nd > N) ? N : nd;
                }
            }
        }
    }

    // 3. Fixpoint propagation using compact L1-resident need table
    bool changed = true;
    while (changed) {
        changed = false;
        for (int idx = 0; idx < active_cnt; idx++) {
            const int i = active_i[idx];
            const int req = rem_vis[i];
            int can_count = 0;
            const int* row = need[idx];
            for (int j = m; j < N; j++) {
                if (row[j] <= UB[j]) can_count++;
            }
            if (can_count < req) return;
            if (can_count == req) {
                for (int j = m; j < N; j++) {
                    const int nd = row[j];
                    if (nd <= UB[j] && nd > LB[j]) {
                        LB[j] = nd;
                        if (LB[j] > UB[j]) return;
                        changed = true;
                    }
                }
            }
        }
    }

    // 4. Tighter per-column edge capacity check
    int max_absorb = 0;
    const int m1_active = (m > 0 && rem_vis[m - 1] > 0) ? 1 : 0;
    for (int j = m; j < N; j++) {
        int can_see_j = m1_active;
        for (int idx = 0; idx < active_cnt; idx++) {
            if (need[idx][j] <= UB[j]) can_see_j++;
        }
        int deg_cap = UB[j] - (j < N - 1 ? 1 : 0);
        if (deg_cap < 0) deg_cap = 0;
        max_absorb += (can_see_j < deg_cap) ? can_see_j : deg_cap;
    }
    if (rem_sum > max_absorb) return;

    // 5. Tighten LB[m] and UB[m] reusing cached need[idx][m]
    if (m > 0) {
        int min_vis_left = 1; // always sees m-1
        int max_vis_left = 1;
        for (int idx = 0; idx < active_cnt; idx++) {
            const int nd = need[idx][m];
            if (nd <= LB[m]) min_vis_left++;
            if (nd <= UB[m]) max_vis_left++;
        }
        const int min_vis_right = (m < N - 1) ? 1 : 0;
        const int max_vis_right = N - 1 - m;
        if (LB[m] < min_vis_left + min_vis_right) LB[m] = min_vis_left + min_vis_right;
        if (UB[m] > max_vis_left + max_vis_right) UB[m] = max_vis_left + max_vis_right;
        if (LB[m] > UB[m]) return;
    }

    // 6. Branch on v in [LB[m], UB[m]]
    int saved_rem[MAXN];
    if (m > 0) memcpy(saved_rem, rem_vis, m * sizeof(int));

    const int min_rem_m = (m < N - 1) ? 1 : 0;
    const int max_rem_m = N - 1 - m;

    for (int v = LB[m]; v <= UB[m]; v++) {
        seq[m] = v;
        int vis_left = 0;
        bool ok = true;

        int mod_idx[MAXN], old_p[MAXN], old_q[MAXN];
        int mod_cnt = 0;
        int next_jz[MAXN];
        int next_jz_cnt = 0;

        for (int i = 0; i < m; i++) {
            const int dy = v - seq[i];
            const int dx = m - i;
            if (i == m - 1 || dy * max_q[i] >= max_p[i] * dx) {
                if (saved_rem[i] == 0) {
                    ok = false;
                    break;
                }
                vis_left++;
                const int nr = saved_rem[i] - 1;
                rem_vis[i] = nr;
                if (nr == 0) next_jz[next_jz_cnt++] = i;

                mod_idx[mod_cnt] = i;
                old_p[mod_cnt] = max_p[i];
                old_q[mod_cnt] = max_q[i];
                mod_cnt++;
                max_p[i] = dy;
                max_q[i] = dx;
            }
        }

        if (ok) {
            const int rem_m = v - vis_left;
            if (rem_m >= min_rem_m && rem_m <= max_rem_m) {
                rem_vis[m] = rem_m;
                dfs(m + 1, strictly_less || (v < target[m]), UB, next_jz, next_jz_cnt);
                if (found || aborted) return;
            }
        }

        for (int k = 0; k < mod_cnt; k++) {
            const int i = mod_idx[k];
            rem_vis[i] = saved_rem[i];
            max_p[i] = old_p[k];
            max_q[i] = old_q[k];
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string line;
    while (getline(cin, line)) {
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
        dfs(0, false, nullptr, nullptr, 0);
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
