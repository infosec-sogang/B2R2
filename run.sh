#!/bin/bash

./src/RearEnd/BinExplorer/bin/Debug/net8.0/B2R2.RearEnd.BinExplorer --isa=evm \
  --disable-codecopy --evmabi=B1/abi/$1.abi B1/bin/$1.bc

#./src/RearEnd/BinExplorer/bin/Debug/net8.0/B2R2.RearEnd.BinExplorer --isa=evm \
#  --evmabi=B1/abi/$1.abi B1/bin/$1.bc
