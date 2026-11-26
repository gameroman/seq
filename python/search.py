import time
from ortools.sat.python import cp_model

seq_17 = [
    1,
    3,
    2, 5,
    2, 4, 2, 6,
    2, 5, 3, 3, 7,
    2, 6, 2, 4, 4, 2, 8,
    2, 7, 2, 4, 5, 3, 4, 9,
    2, 8, 2, 4, 5, 4, 5, 2, 10,
    2, 9, 6, 5, 4, 6, 6, 3, 5, 2, 11, 11,
    2, 4, 3, 6, 2, 5, 2, 7, 7, 2, 5, 2, 5, 2, 8, 2, 9, 2, 8, 2, 4, 4, 3, 8, 2, 7, 2, 5, 4, 4, 12, 2, 12,
    2, 4, 3, 6, 2, 5, 2, 8, 2, 4, 4, 2, 9, 2, 5, 2, 5, 2, 10, 2, 4, 3, 7, 3, 4, 3, 11, 2, 8, 2, 4, 3, 7, 3, 3, 9, 2, 5, 2, 6, 3, 4, 2, 13, 2, 13,
    2, 4, 3, 6, 2, 5, 2, 8, 2, 4, 4, 2, 9, 2, 5, 2, 5, 2, 10, 2, 4, 3, 7, 3, 4, 3, 11, 4, 4, 5, 2, 9, 3, 4, 3, 12, 2, 7, 2, 7, 3, 4, 2, 8, 2, 10, 4, 3, 6, 2, 6, 3, 4, 2, 14, 2, 14,
    2, 4, 3, 6, 2, 5, 2, 8, 2, 4, 4, 2, 9, 2, 5, 2, 5, 2, 10, 2, 4, 3, 7, 3, 4, 3, 11, 4, 4, 5, 2, 9, 3, 4, 3, 12, 5, 4, 5, 5, 2, 10, 4, 4, 4, 13, 12, 2, 4, 5, 3, 6, 6, 5, 6, 12, 3, 3, 12, 2, 7, 2, 5, 4, 9, 5, 3, 6, 2, 7, 2, 15, 2, 15,
    2, 4, 3, 6, 2, 5, 2, 8, 2, 4, 4, 2, 9, 2, 5, 2, 5, 2, 10, 2, 4, 3, 7, 3, 4, 3, 11, 4, 4, 5, 2, 9, 3, 4, 3, 12, 5, 4, 5, 5, 2, 10, 4, 4, 4, 13, 3, 4, 3, 8, 2, 7, 4, 3, 7, 2, 14, 2, 4, 4, 3, 9, 2, 5, 4, 4, 13, 8, 7, 6, 5, 8, 8, 4, 5, 4, 2, 11, 2, 16, 2, 16,
    2, 4, 3, 6, 2, 5, 2, 8, 2, 4, 4, 2, 9, 2, 5, 2, 5, 2, 10, 2, 4, 3, 7, 3, 4, 3, 11, 4, 4, 5, 2, 9, 3, 4, 3, 12, 5, 4, 5, 5, 2, 10, 4, 4, 4, 13, 3, 4, 3, 8, 2, 7, 4, 3, 7, 2, 14, 6, 6, 6, 6, 6, 12, 2, 6, 5, 5, 5, 15, 4, 4, 5, 3, 9, 3, 4, 3, 13, 2, 7, 2, 7, 3, 3, 8, 8, 2, 5, 6, 5, 3, 7, 10, 17, 2, 17
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


def step_height(
    seq,
    prev_spine,
    h,
    b1_max_left=None,
    b1_max_len=35,
    b1_time=25.0,
    b2_cap=None,
    b2_max_len=60,
    b2_time=60.0,
):
    u0 = len(seq) - 3
    u1 = len(seq) - 1
    if b1_max_left is None:
        b1_max_left = h - 5
    if b2_cap is None:
        b2_cap = h - 2

    base1 = seq + prev_spine
    over1, unsat1 = verify_state(base1, f"h={h}->spine")
    if over1:
        print(f"  ERROR: spine overshot at h={h}")
        return None, None, None
    p_mid1 = len(base1) - 1

    base2 = None
    b1_info = None
    for length in range(5, b1_max_len + 1):
        target_idx = p_mid1 + length
        st, dt, res = solve_subvalley(
            base1,
            target_idx,
            h - 1,
            interior_cap=h - 3,
            max_time=b1_time,
            exact_interior=True,
            must_sat_indices={p_mid1},
            target_max_left=b1_max_left,
        )
        if st != "STATIC_INFEASIBLE":
            print(f"  Bridge1 {p_mid1}({h-2}) -> {target_idx}({h-1}) [len {length}]: {st} in {dt:.2f}s")
        if res is not None:
            base2 = res
            b1_info = (p_mid1 + 1, target_idx, length, dt, res[p_mid1 + 1:])
            break
    if base2 is None:
        print(f"  FAILED Bridge1 at h={h}")
        return None, None, None
    over2, unsat2 = verify_state(base2, f"h={h}->b1")
    p_mid2 = len(base2) - 1
    new_spine = base2[u1 + 1:]

    base3 = None
    b2_info = None
    for length in range(8, b2_max_len + 1):
        target_idx = p_mid2 + length
        st, dt, res = solve_subvalley(
            base2,
            target_idx,
            h + 1,
            interior_cap=b2_cap,
            max_time=b2_time,
            exact_interior=True,
            must_sat_indices={u0, u1, p_mid2},
            target_exact_left=h - 2,
        )
        if st != "STATIC_INFEASIBLE":
            print(f"  Bridge2 {p_mid2}({h-1}) -> {target_idx}({h+1}) [len {length}]: {st} in {dt:.2f}s")
        if res is not None:
            base3 = res
            b2_info = (p_mid2 + 1, target_idx, length, dt, res[p_mid2 + 1:])
            break
    if base3 is None:
        print(f"  FAILED Bridge2 at h={h}")
        return None, None, {"base2": base2, "new_spine": new_spine, "b1": b1_info}

    new_seq = base3 + [2, h + 1]
    over3, unsat3 = verify_state(new_seq, f"seq_{h+1}")
    return new_seq, new_spine, {"b1": b1_info, "b2": b2_info, "spine_len": len(prev_spine)}


if __name__ == "__main__":
    cur_seq = seq_17
    cur_spine = seq_17[341:410]  # immediately after [16, 2, 16] through peak 15
    assert cur_spine[-1] == 15, f"Wrong spine end: {cur_spine[-1]}"

    over0, unsat0 = verify_state(cur_seq, "init_17")
    assert not over0, f"Input sequence has overshoots: {over0}"

    seqs = {17: cur_seq}

    for h in [17, 18, 19]:
        print(f"\n================ ADVANCING {h} -> {h+1} ================")
        nxt_seq, nxt_spine, info = step_height(
            cur_seq,
            cur_spine,
            h,
            b1_max_len=35,
            b1_time=25.0,
            b2_max_len=100,
            b2_time=300.0,
        )
        if nxt_seq is not None:
            cur_seq, cur_spine = nxt_seq, nxt_spine
            seqs[h + 1] = cur_seq
            out_file = f"seq_{h+1}.txt"
            with open(out_file, "w") as f:
                f.write(" ".join(map(str, cur_seq)) + "\n")
            print(f"  SUCCESS h={h+1}! len={len(cur_seq)} | saved to {out_file}")
            print(f"  b1={info['b1'][4]}")
            print(f"  b2={info['b2'][4]}")
        else:
            print(f"  Stopped at h={h} -> {h+1}")
            break
