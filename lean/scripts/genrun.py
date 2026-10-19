import sys, os, glob
out = sys.argv[1]  # BMLean/BMLean
hubs = sorted(os.path.basename(p)[:-5] for p in glob.glob(f"{out}/Data/Hub*.lean"))
trees = sorted(os.path.basename(p)[:-5] for p in glob.glob(f"{out}/Data/Tree*.lean"))
os.makedirs(f"{out}/Run", exist_ok=True)
for h in hubs:
    n = h[3:]
    open(f"{out}/Run/{h}.lean", "w").write(f"import BMLean.Tables\nimport BMLean.Data.{h}\n\nnamespace BMC\n\ntheorem hubOk_{n} : hubChunkOk (parseRows BMD.hub{n}) = true := by native_decide\n\nend BMC\n")
for t in trees:
    n = t[4:]
    open(f"{out}/Run/{t}.lean", "w").write(f"import BMLean.Tables\nimport BMLean.Data.{t}\n\nnamespace BMC\n\ntheorem treeOk_{n} : treeChunkOk (parseTrees BMD.tree{n}) = true := by native_decide\n\nend BMC\n")
imp = "".join(f"import BMLean.Data.{x}\n" for x in hubs + trees)
rl = ",\n  ".join(f"parseRows BMD.hub{h[3:]}" for h in hubs)
tl = ",\n  ".join(f"parseTrees BMD.tree{t[4:]}" for t in trees)
open(f"{out}/AllData.lean", "w").write(f"import BMLean.Tables\n{imp}\nnamespace BMC\n\ndef allRowsL : List (List Row) := [\n  {rl}]\n\ndef allTreesL : List (List TreeRec) := [\n  {tl}]\n\nend BMC\n")
open(f"{out}/Run/Cover.lean", "w").write("import BMLean.AllData\n\nnamespace BMC\n\ntheorem cover_ok : coverOk allRowsL.flatten allTreesL.flatten = true := by native_decide\n\nend BMC\n")
open(f"{out}/Run/Roots.lean", "w").write("import BMLean.Tables\n\nnamespace BMC\n\ntheorem roots_ok : rootsOk = true := by native_decide\n\nend BMC\n")
imp2 = "".join(f"import BMLean.Run.{x}\n" for x in hubs + trees) + "import BMLean.Run.Cover\nimport BMLean.Run.Roots\n"
hs = ", ".join(f"hubOk_{h[3:]}" for h in hubs)
ts = ", ".join(f"treeOk_{t[4:]}" for t in trees)
open(f"{out}/AllRun.lean", "w").write(f"""{imp2}
namespace BMC

theorem all_hub_ok : allRowsL.all hubChunkOk = true := by
  simp only [allRowsL, List.all_cons, List.all_nil, Bool.and_true, {hs}]

theorem all_tree_ok : allTreesL.all treeChunkOk = true := by
  simp only [allTreesL, List.all_cons, List.all_nil, Bool.and_true, {ts}]

end BMC
""")
print(len(hubs), len(trees))
