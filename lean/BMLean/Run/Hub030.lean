import BMLean.Tables
import BMLean.Data.Hub030

namespace BMC

theorem hubOk_030 : hubChunkOk (parseRows BMD.hub030) = true := by native_decide

end BMC
