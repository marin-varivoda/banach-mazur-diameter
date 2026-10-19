import BMLean.Tables
import BMLean.Data.Hub016

namespace BMC

theorem hubOk_016 : hubChunkOk (parseRows BMD.hub016) = true := by native_decide

end BMC
