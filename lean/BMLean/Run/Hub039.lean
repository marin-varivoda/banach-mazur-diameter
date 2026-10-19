import BMLean.Tables
import BMLean.Data.Hub039

namespace BMC

theorem hubOk_039 : hubChunkOk (parseRows BMD.hub039) = true := by native_decide

end BMC
