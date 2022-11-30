#!/usr/bin/env bash

set -euo pipefail
set -x 

user=${SUDO_USER:-$USER}

ip tuntap add name tap1 mode tap user $user
ip addr add 10.0.0.1/24 dev tap1
ip link set addr 02:aa:aa:aa:aa:aa dev tap1
ip link set up dev tap1
ip neigh add 10.0.0.2 lladdr 02:bb:bb:bb:bb:bb dev tap1
iptables -D INPUT -i tap1 -j ACCEPT 2> /dev/null || true # ignore error
iptables -I INPUT -i tap1 -j ACCEPT 
