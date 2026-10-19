import BMLean.Tables
import BMLean.Data.Hub062

namespace BMC

theorem hubOk_062 : hubChunkOk (parseRows BMD.hub062) = true := by native_decide

end BMC
