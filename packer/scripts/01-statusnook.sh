#!/bin/bash

cat <<EOF >/etc/systemd/system/statusnook-script.service
[Unit]
Description=Statusnook script
After=network.target

[Service]
Type=simple
ExecStart=/bin/bash -c '/usr/bin/curl -fsSL "get.statusnook.com" | /usr/bin/bash'
ExecStartPost=/usr/bin/systemctl disable statusnook-script
ExecStartPost=/usr/bin/rm /etc/systemd/system/statusnook-script.service

[Install]
WantedBy=multi-user.target
EOF

systemctl enable statusnook-script
