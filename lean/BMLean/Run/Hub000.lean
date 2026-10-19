import BMLean.Tables
import BMLean.Data.Hub000

namespace BMC

theorem hubOk_000 : hubChunkOk (parseRows BMD.hub000) = true := by native_decide

end BMC
