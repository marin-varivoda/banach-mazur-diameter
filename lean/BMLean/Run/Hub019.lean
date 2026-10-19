import BMLean.Tables
import BMLean.Data.Hub019

namespace BMC

theorem hubOk_019 : hubChunkOk (parseRows BMD.hub019) = true := by native_decide

end BMC
