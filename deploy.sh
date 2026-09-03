#!/bin/bash
# JinShu deploy 2026-09-03 #2: git bundle fetch (=push 3 commits) + api.py/items.json
# Run as root on 49.0.255.47 (VNC):
#   curl -sL https://raw.githubusercontent.com/a38856234/jinshu-deploy/main/deploy.sh | bash
set -e
RAW=https://raw.githubusercontent.com/a38856234/jinshu-deploy/main
D=/tmp/jinshu-deploy
rm -rf $D; mkdir -p $D; cd $D

echo "[1/6] download"
curl -sfO $RAW/api.py
curl -sfO $RAW/items.json
curl -sfO $RAW/jinshu.bundle

echo "[2/6] md5 gate"
cat > md5.txt <<'EOF'
58147d9cb79b53c7bf7022e436c8455c  api.py
40048152f45d7943fbd169967414064f  items.json
b02bbb8ca374f3142edadab9c6f798aa  jinshu.bundle
EOF
md5sum -c md5.txt

echo "[3/6] git fetch bundle into bare repo (=push e4035cb)"
sudo -u git git -C /srv/git/jinshu.git fetch $D/jinshu.bundle 'refs/heads/main:refs/heads/main'
NOW=$(sudo -u git git -C /srv/git/jinshu.git rev-parse main)
case "$NOW" in
  e4035cb*) echo "git main -> ${NOW:0:7} (expected e4035cb)";;
  *) echo "GIT HEAD MISMATCH: $NOW (expected e4035cb...)"; exit 1;;
esac

echo "[4/6] backup + install files"
TS=$(date +%Y%m%d-%H%M%S)
mkdir -p /srv/cloudsave/bak-$TS
for f in api.py items.json; do
  if [ -f /srv/cloudsave/$f ]; then cp -a /srv/cloudsave/$f /srv/cloudsave/bak-$TS/; fi
done
install -o deployer -g deployer -m 644 api.py /srv/cloudsave/api.py
install -o deployer -g deployer -m 644 items.json /srv/cloudsave/items.json

echo "[5/6] restart service"
systemctl restart cloudsave
sleep 1

echo "[6/6] health check"
S=$(systemctl is-active cloudsave.service)
P1=$(curl -s http://127.0.0.1:8765/api/save/ping)
P2=$(curl -s -H "Host: jsqxz.byeyb.com" http://127.0.0.1/api/save/ping)
echo "service=$S  ping_direct=$P1  ping_vhost=$P2"
if [ "$S" != "active" ] || [ -z "$P1" ] || -z "$(echo $P1 | grep ok)" || [ -z "$(echo $P2 | grep ok)" ]; then
  echo "!! HEALTH FAIL -> rollback"
  cp -a /srv/cloudsave/bak-$TS/api.py /srv/cloudsave/api.py
  if [ -f /srv/cloudsave/bak-$TS/items.json ]; then
    cp -a /srv/cloudsave/bak-$TS/items.json /srv/cloudsave/items.json
  else
    rm -f /srv/cloudsave/items.json
  fi
  systemctl restart cloudsave; sleep 1
  echo "rollback: service=$(systemctl is-active cloudsave.service)"
  exit 1
fi
echo "DEPLOY DONE (backup: /srv/cloudsave/bak-$TS)"
