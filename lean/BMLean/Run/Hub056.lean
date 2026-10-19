import BMLean.Tables
import BMLean.Data.Hub056

namespace BMC

theorem hubOk_056 : hubChunkOk (parseRows BMD.hub056) = true := by native_decide

end BMC
