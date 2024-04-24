#!/bin/bash

# Copyright (c) 2024 Goksan
# The original content was modified to add "-o DPkg::Lock::Timeout=-1" on lines 27-30
# The original content was modified to add "sleep 10`" on line 26

# DigitalOcean Marketplace Image Validation Tool
# © 2021 DigitalOcean LLC.
# This code is licensed under Apache 2.0 license (see LICENSE.md for details)

set -o errexit

# Ensure /tmp exists and has the proper permissions before
# checking for security updates
# https://github.com/digitalocean/marketplace-partners/issues/94
if [[ ! -d /tmp ]]; then
  mkdir /tmp
fi
chmod 1777 /tmp

if [ -n "$(command -v yum)" ]; then
  yum update -y
  yum clean all
elif [ -n "$(command -v apt-get)" ]; then
  export DEBIAN_FRONTEND=noninteractive
  sleep 10
  apt-get -o DPkg::Lock::Timeout=-1 -y update
  apt-get -o DPkg::Lock::Timeout=-1 -o Dpkg::Options::="--force-confold" upgrade -q -y --force-yes
  apt-get -o DPkg::Lock::Timeout=-1 -y autoremove
  apt-get -o DPkg::Lock::Timeout=-1 -y autoclean
fi

rm -rf /tmp/* /var/tmp/*
history -c
cat /dev/null > /root/.bash_history
unset HISTFILE
find /var/log -mtime -1 -type f -exec truncate -s 0 {} \;
rm -rf /var/log/*.gz /var/log/*.[0-9] /var/log/*-????????
rm -rf /var/lib/cloud/instances/*
rm -f /root/.ssh/authorized_keys /etc/ssh/*key*
touch /etc/ssh/revoked_keys
chmod 600 /etc/ssh/revoked_keys

# Securely erase the unused portion of the filesystem
GREEN='\033[0;32m'
NC='\033[0m'
printf "\n${GREEN}Writing zeros to the remaining disk space to securely
erase the unused portion of the file system.
Depending on your disk size this may take several minutes.
The secure erase will complete successfully when you see:${NC}
    dd: writing to '/zerofile': No space left on device\n
Beginning secure erase now\n"

dd if=/dev/zero of=/zerofile bs=4096 || rm /zerofile
