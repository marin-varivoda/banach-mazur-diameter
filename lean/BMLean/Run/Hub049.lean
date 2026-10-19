import BMLean.Tables
import BMLean.Data.Hub049

namespace BMC

theorem hubOk_049 : hubChunkOk (parseRows BMD.hub049) = true := by native_decide

end BMC
