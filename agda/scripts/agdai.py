#!/usr/bin/env python3
# A tiny driver over `agda --interaction-json` — the same backend Emacs
# agda-mode drives — so proof development gets interactive goal + context
# display from the shell (no editor needed).
#
#   scripts/agdai.py FILE            load FILE, print errors + every goal's
#                                    context and type (like C-c C-l / C-c C-,)
#   scripts/agdai.py FILE N          just goal N, verbose
#
# Run from the agda/ dir (needs the project's .agda-lib on the include path).
import json, subprocess, sys, os

def run(path, maxgoals=60):
    absn = os.path.abspath(path)
    cmds = [f'IOTCM "{absn}" NonInteractive Direct (Cmd_load "{absn}" [])']
    for i in range(maxgoals):
        cmds.append(f'IOTCM "{absn}" NonInteractive Direct '
                    f'(Cmd_goal_type_context Simplified {i} noRange "")')
    env = dict(os.environ, LC_ALL="C.UTF-8", LANG="C.UTF-8")
    p = subprocess.run(["agda", "--interaction-json"], input="\n".join(cmds)+"\n",
                       capture_output=True, text=True, env=env, timeout=600)
    goals, ctx, errors, warns = {}, {}, [], []
    for line in p.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"): continue
        try: o = json.loads(line)
        except json.JSONDecodeError: continue
        info = o.get("info", {})
        k = info.get("kind")
        if k == "AllGoalsWarnings":
            for g in info.get("visibleGoals", []):
                cobj = g.get("constraintObj", {})
                rng = cobj.get("range", [{}])
                ln = rng[0].get("start", {}).get("line") if rng else None
                goals[cobj.get("id")] = (g.get("type"), ln)
            errors = info.get("errors", []); warns = info.get("warnings", [])
        elif k == "Error":
            errors.append(info.get("message") or json.dumps(info)[:400])
        elif o.get("kind") == "DisplayInfo" and info.get("kind") == "GoalSpecific":
            gi = info.get("goalInfo", {})
            iid = info.get("interactionPoint", {}).get("id")
            ctx[iid] = (gi.get("type"),
                        [(e.get("reifiedName"), e.get("binding")) for e in gi.get("entries", [])])
    # top-level errors (parse/scope) sometimes only appear as bare Error lines
    for line in p.stdout.splitlines():
        if '"kind":"DisplayInfo"' in line and '"error"' in line.lower() and "Error" in line:
            try:
                o = json.loads(line); m = o.get("info", {}).get("message")
                if m and m not in errors: errors.append(m)
            except Exception: pass
    return goals, ctx, errors, warns

def main():
    path = sys.argv[1]
    only = int(sys.argv[2]) if len(sys.argv) > 2 else None
    goals, ctx, errors, warns = run(path)
    if errors:
        print("=== ERRORS ===")
        for e in errors: print(e); print("-"*40)
    if warns:
        print(f"=== {len(warns)} warning(s) ===")
    if not goals:
        print("No open goals." if not errors else "(goals unavailable — fix errors)")
        return
    for gid in sorted(g for g in goals if g is not None):
        if only is not None and gid != only: continue
        typ, ln = goals[gid]
        gtyp, entries = ctx.get(gid, (typ, []))
        print(f"?{gid}  (line {ln})")
        for name, binding in entries:
            print(f"    {name} : {binding}")
        print(f"  ⊢ {gtyp}")
        print()

if __name__ == "__main__":
    main()
