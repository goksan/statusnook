#!/bin/bash

PORT=80

for arg in "$@"
do
    case $arg in
        -port)
        PORT="$2"
        shift
        shift
        ;;
    esac
done


useradd statusnook --system -m

cd /home/statusnook


case $(uname -m) in
    x86_64)
        goarch="amd64"
        ;;
    aarch64)
        goarch="arm64"
        ;;
    *)
        echo "unknown arch"
        exit 1
        ;;
esac

curl -fsSL https://get.statusnook.com/statusnook_linux_${goarch}_v0.3.0 -o /home/statusnook/statusnook

chmod +x /home/statusnook/statusnook

cat <<EOF >/etc/systemd/system/statusnook.service
[Unit]
Description=Statusnook
After=network.target

[Service]
Type=simple
Restart=always
User=statusnook
WorkingDirectory=/home/statusnook
ExecStart=/home/statusnook/statusnook --port $PORT
EOF
if [ "$PORT" -eq 80 ]; then
    echo -e "AmbientCapabilities=CAP_NET_BIND_SERVICE\n" >> /etc/systemd/system/statusnook.service
else
    echo -e "" >> /etc/systemd/system/statusnook.service
fi
cat <<EOF >>/etc/systemd/system/statusnook.service
[Install]
WantedBy=multi-user.target
EOF

systemctl enable statusnook > /dev/null 2>&1
systemctl start statusnook

echo "Self-signed certificate SHA-256 fingerprint: $(su - statusnook -c "/home/statusnook/statusnook -generate-self-signed-cert")"

echo -e '\n\033[0;32mStatusnook successfully installed!\033[0m'
echo "To finalize your Statusnook instance setup, navigate to https://<your-ip-address-or-domain> in a web browser"
