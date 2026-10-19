import BMLean.AllData

namespace BMC

theorem cover_ok : coverOk allRowsL.flatten allTreesL.flatten = true := by native_decide

end BMC
