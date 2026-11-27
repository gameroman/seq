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
long long node_limit = 100'000'000'000LL;
bool aborted = false;

// Prefix locking state: locks the first (prev_N / 3) elements of prev_best
// whenever prev_best is lexicographically <= target on that prefix.
vector<int> prev_best;
int lock_prefix = 0;

// Depth-indexed scratch buffers (prevents stack overflow on Windows for N >= 140)
int UB_buf[MAXN][MAXN];
int LB_buf[MAXN][MAXN];
int saved_rem_buf[MAXN][MAXN];
int active_i_buf[MAXN][MAXN];
int mod_idx_buf[MAXN][MAXN], old_p_buf[MAXN][MAXN], old_q_buf[MAXN][MAXN];
int next_jz_buf[MAXN][MAXN];

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

    int* UB = UB_buf[m];
    int* LB = LB_buf[m];
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

    // Force prev_best's first third directly (even when target[m] was suboptimal earlier)
    if (m < lock_prefix) {
        const int forced = prev_best[m];
        if (forced < LB[m] || forced > UB[m]) return;
        LB[m] = UB[m] = forced;
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
    static int need[MAXN][MAXN];
    int* active_i = active_i_buf[m];
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

    // 4. Tighten LB[m] and UB[m] reusing cached need[idx][m]
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

    // 5. Per-column edge capacity + mandatory internal edge & parity check
    int max_absorb = 0;
    int sum_ub = 0;
    int sum_lb = 0;
    const int m1_active = (m > 0 && rem_vis[m - 1] > 0) ? 1 : 0;
    for (int j = m; j < N; j++) {
        sum_ub += UB[j];
        sum_lb += LB[j];
        int can_see_j = m1_active;
        for (int idx = 0; idx < active_cnt; idx++) {
            if (need[idx][j] <= UB[j]) can_see_j++;
        }
        int deg_cap = UB[j] - (j < N - 1 ? 1 : 0);
        if (deg_cap < 0) deg_cap = 0;
        max_absorb += (can_see_j < deg_cap) ? can_see_j : deg_cap;
    }
    if (rem_sum > max_absorb) return;
    if (sum_ub < rem_sum + 2 * (N - 1 - m)) return;
    if (sum_lb == sum_ub && ((sum_ub - rem_sum) & 1)) return;

    // 6. Branch on v in [LB[m], UB[m]]
    int* saved_rem = saved_rem_buf[m];
    if (m > 0) memcpy(saved_rem, rem_vis, m * sizeof(int));

    int* mod_idx = mod_idx_buf[m];
    int* old_p = old_p_buf[m];
    int* old_q = old_q_buf[m];
    int* next_jz = next_jz_buf[m];

    const int min_rem_m = (m < N - 1) ? 1 : 0;
    const int max_rem_m = N - 1 - m;

    for (int v = LB[m]; v <= UB[m]; v++) {
        seq[m] = v;
        int vis_left = 0;
        bool ok = true;
        int mod_cnt = 0;
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

        // Lock up to (prev_N / 3) elements from prev_best whenever prev_best <= target
        // lexicographically on that prefix (overrides early suboptimal terms in target).
        lock_prefix = 0;
        if (!prev_best.empty() && (int)prev_best.size() < N) {
            int third = (int)prev_best.size() / 3;
            bool leq = true;
            for (int i = 0; i < third; i++) {
                if (prev_best[i] < target[i]) break;
                if (prev_best[i] > target[i]) {
                    leq = false;
                    break;
                }
            }
            if (leq) lock_prefix = third;
        }

        found = false;
        aborted = false;
        nodes = 0;

        auto t0 = chrono::steady_clock::now();
        dfs(0, false, nullptr, nullptr, 0);
        auto t1 = chrono::steady_clock::now();
        double ms = chrono::duration<double, milli>(t1 - t0).count();

        if (found) {
            prev_best.assign(found_seq, found_seq + N);
            for (int i = 0; i < N; i++) cout << found_seq[i] << (i + 1 == N ? "" : " ");
            cout << "  // IMPROVED (n=" << N << ", lock=" << lock_prefix << ", nodes=" << nodes << ", " << ms << "ms)\n";
        } else {
            if (!aborted) prev_best.assign(target, target + N);
            for (int i = 0; i < N; i++) cout << target[i] << (i + 1 == N ? "" : " ");
            cout << "  // " << (aborted ? "ABORTED" : "OPTIMAL") << " (n=" << N << ", lock=" << lock_prefix << ", nodes=" << nodes << ", " << ms << "ms)\n";
        }
        cout.flush();
    }
    return 0;
}
