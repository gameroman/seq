import time
from ortools.sat.python import cp_model


base_15 = [
    1, 3, 2, 5,
    2, 4, 2, 7,
    2, 4, 4, 2, 8,
    2, 5, 2, 5, 2, 9,
    2, 4, 3, 7, 3, 4, 3, 10,
    2, 4, 3, 7, 3, 4, 4, 2, 11,
    2, 6, 2, 5, 2, 8, 3, 4, 3, 12,
    2, 4, 3, 7, 3, 3, 7, 3, 4, 2, 13,
    2, 4, 3, 7, 2, 6, 2, 7, 3, 4, 2, 14,
    2, 4, 3, 7, 2, 5, 2, 8, 3, 4, 4, 2, 15,
    2, 9, 2, 9, 2, 9, 2, 9, 2, 9, 2, 9, 2, 16,
    2, 8, 2, 5, 2, 8, 2, 8, 2, 6, 2, 9, 3, 3, 17,
    2, 10, 2, 10, 2, 10, 2, 10, 2, 10, 2, 10, 2, 10, 2, 18,
    5, 5, 5, 5, 13, 5, 4, 4, 8, 2, 8, 2, 7, 3, 8, 2, 19,
    2, 11, 2, 11, 2, 11, 2, 11, 2, 11, 2, 11, 2, 11, 2, 11, 2, 20,
    2, 9, 2, 7, 2, 6, 2, 9, 2, 9, 2, 7, 2, 7, 2, 10, 3, 3, 21,
    2, 12, 2, 12, 2, 12, 2, 12, 2, 12, 2, 12, 2, 12, 2, 12, 2, 12, 2, 22
]

def full_state(s):
    n = len(s)
    vis, mr = [0] * n, [None] * n
    for i in range(n):
        lv, bd = 0, None
        for j in range(i - 1, -1, -1):
            dy, dx = s[j] - s[i], i - j
            if bd is None or dy * bd[1] >= bd[0] * dx:
                lv += 1
                bd = (dy, dx)
        rv, bd = 0, None
        for j in range(i + 1, n):
            dy, dx = s[j] - s[i], j - i
            if bd is None or dy * bd[1] >= bd[0] * dx:
                rv += 1
                bd = (dy, dx)
        vis[i], mr[i] = lv + rv, bd
    return vis, mr


def verify_state(s, label=""):
    vis, mr = full_state(s)
    over = [(i, s[i], vis[i]) for i in range(len(s)) if vis[i] > s[i]]
    unsat = [(i, s[i], vis[i], mr[i]) for i in range(len(s)) if vis[i] < s[i]]
    print(f"[{label}] len={len(s)} | over={over} | unsat={unsat}")
    return over, unsat


def solve_subvalley(
    base,
    target_idx,
    target_val,
    interior_cap,
    max_time=12.0,
    exact_interior=True,
    must_sat_indices=None,
    target_exact_left=None,
    target_max_left=None,
):
    n0 = len(base)
    N = target_idx + 1
    vis0, mr0 = full_state(base)
    sat = [i for i in range(n0) if vis0[i] == base[i]]
    unsat = [i for i in range(n0) if vis0[i] < base[i]]

    U = {}
    for k in range(n0, N):
        U[k] = min((base[i] * mr0[i][1] + mr0[i][0] * (k - i) - 1) // mr0[i][1] for i in sat)
    if U[target_idx] < target_val:
        return "STATIC_INFEASIBLE", 0.0, None

    model = cp_model.CpModel()
    s = {i: base[i] for i in range(n0)}
    for k in range(n0, target_idx):
        ub = min(U[k], interior_cap)
        if ub < 2:
            return "STATIC_INFEASIBLE", 0.0, None
        s[k] = model.NewIntVar(2, ub, f"s_{k}")
    s[target_idx] = target_val

    is2 = {}
    for k in range(n0, target_idx):
        is2[k] = model.NewBoolVar(f"is2_{k}")
        model.Add(s[k] == 2).OnlyEnforceIf(is2[k])
        model.Add(s[k] != 2).OnlyEnforceIf(is2[k].Not())
        if k > n0:
            model.Add(is2[k - 1] + is2[k] <= 1)

    v = {}
    for i in unsat + list(range(n0, N)):
        for j in range(max(n0, i + 1), N):
            if j == i + 1:
                v[(i, j)] = 1
                continue
            vij = model.NewBoolVar(f"v_{i}_{j}")
            v[(i, j)] = vij
            blockers = []
            already_blocked = False
            for m in range(i + 1, j):
                if m < n0 and i < n0 and j == target_idx:
                    if base[m] * (j - i) > base[i] * (j - m) + target_val * (m - i):
                        already_blocked = True
                        break
                    else:
                        continue
                bm = model.NewBoolVar(f"b_{i}_{m}_{j}")
                model.Add(s[m] * (j - i) >= s[i] * (j - m) + s[j] * (m - i) + 1).OnlyEnforceIf(bm)
                model.Add(s[m] * (j - i) <= s[i] * (j - m) + s[j] * (m - i)).OnlyEnforceIf(bm.Not())
                blockers.append(bm)
            if already_blocked:
                model.Add(vij == 0)
            else:
                for b in blockers:
                    model.AddImplication(vij, b.Not())
                model.AddBoolOr([vij] + blockers)

    for u in unsat:
        add_vis = sum(v[(u, j)] for j in range(n0, N))
        if must_sat_indices and u in must_sat_indices:
            model.Add(vis0[u] + add_vis == base[u])
        else:
            model.Add(vis0[u] + add_vis <= base[u])

    for k in range(n0, target_idx):
        vis_k = (
            sum(v[(i, k)] for i in unsat)
            + sum(v[(i, k)] for i in range(n0, k))
            + sum(v[(k, j)] for j in range(k + 1, N))
        )
        if exact_interior:
            model.Add(vis_k == s[k])
        else:
            model.Add(vis_k <= s[k])

    vis_t = sum(v[(i, target_idx)] for i in unsat) + sum(v[(i, target_idx)] for i in range(n0, target_idx))
    if target_exact_left is not None:
        model.Add(vis_t == target_exact_left)
    elif target_max_left is not None:
        model.Add(vis_t <= target_max_left)
    else:
        model.Add(vis_t <= target_val - 1)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = max_time
    solver.parameters.num_search_workers = 8
    t0 = time.time()
    status = solver.Solve(model)
    dt = time.time() - t0
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        res = list(base) + [solver.Value(s[k]) for k in range(n0, target_idx)] + [target_val]
        return solver.StatusName(status), dt, res
    return solver.StatusName(status), dt, None


def step_single_peak(seq, h, max_len=30, max_time=30.0):
    u = len(seq) - 1  # index of wall h
    for length in range(h - 2, max_len + 1):
        target_idx = u + length
        st, dt, res = solve_subvalley(
            seq,
            target_idx,
            target_val=h + 1,
            interior_cap=h - 1,
            max_time=max_time,
            exact_interior=True,
            must_sat_indices={u},
            target_exact_left=(h + 1) // 2,
        )
        if res is not None:
            return res, dt
    return None, 0.0


if __name__ == "__main__":
    cur_seq = list(base_15)
    over0, unsat0 = verify_state(cur_seq, "init_15")
    assert not over0, f"Input sequence has overshoots: {over0}"

    for h in range(22, 40):
        print(f"\n================ ADVANCING {h} -> {h+1} ================")
        u = len(cur_seq) - 1
        nxt_seq, dt = step_single_peak(cur_seq, h, max_len=h + 10, max_time=60.0)
        if nxt_seq is not None:
            valley = nxt_seq[u + 1 :]
            cur_seq = nxt_seq
            print(f"  SUCCESS h={h+1} in {dt:.2f}s | total_len={len(cur_seq)}")
            print(f"  valley ({len(valley)} terms): {valley}")

            # Optional: check if reflecting across peak h+1 forms a valid full palindrome
            full_pal = cur_seq + cur_seq[-2::-1]
            over_p, unsat_p = verify_state(full_pal, f"palindrome_{h+1}")
            if not over_p and not unsat_p:
                with open(f"seq_ladder_{h+1}.txt", "w") as f:
                    f.write(" ".join(map(str, full_pal)) + "\n")
        else:
            print(f"  Stopped at h={h} -> {h+1}")
            break
