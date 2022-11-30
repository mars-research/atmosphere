#!/usr/bin/env bash

set -euo pipefail
set -x 

ip link del tap1
iptables -D INPUT -i tap1 -j ACCEPT
