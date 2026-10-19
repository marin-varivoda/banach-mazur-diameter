import BMLean.Tables
import BMLean.Data.Hub001

namespace BMC

theorem hubOk_001 : hubChunkOk (parseRows BMD.hub001) = true := by native_decide

end BMC
