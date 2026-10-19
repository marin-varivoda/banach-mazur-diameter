import BMLean.Tables
import BMLean.Data.Hub054

namespace BMC

theorem hubOk_054 : hubChunkOk (parseRows BMD.hub054) = true := by native_decide

end BMC
