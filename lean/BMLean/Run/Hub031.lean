import BMLean.Tables
import BMLean.Data.Hub031

namespace BMC

theorem hubOk_031 : hubChunkOk (parseRows BMD.hub031) = true := by native_decide

end BMC
