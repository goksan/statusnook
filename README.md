
<p align="center">
  <img width="245px" src="https://github.com/goksan/statusnook/assets/17437810/3823552e-22bf-4bee-82dc-79648135fff6">
</p>

<p align="center">
Effortlessly deploy a status page and start monitoring endpoints in minutes
</p>

![status-page](https://github.com/goksan/statusnook/assets/17437810/0e650d0d-451a-49e3-b7b9-01022c1f931f)

<br>


## Deployment

### Standalone
Quickly deploy Statusnook with managed TLS.

Requires ports 80 and 443
```
curl -fsSL https://get.statusnook.com | sudo bash
```

### Reverse proxy
Deploy Statusnook behind Caddy, NGINX, etc.

```
curl -fsSL https://get.statusnook.com | sudo bash -s -- -port 8000
```

### Docker


#### CLI
```
docker run -d -p 127.0.0.1:8000:8000 -v statusnook-data:/app/statusnook-data --restart always goksan/statusnook
```

#### compose.yaml

```
services:
  statusnook:
    ports:
      - 127.0.0.1:8000:8000
    volumes:
      - statusnook-data:/app/statusnook-data
    restart: always
    image: goksan/statusnook
volumes:
  statusnook-data:
    name: statusnook-data
```

```
docker compose up
```

### One-click cloud templates
<img width="200px" src="https://www.deploytodo.com/do-btn-blue-ghost.svg" alt="Deploy to DO" width="150px">

## Gallery

![monitors](https://github.com/goksan/statusnook/assets/17437810/57424a49-9eec-480a-9450-62af078846f1)
![monitor-logs](https://github.com/goksan/statusnook/assets/17437810/16c0ecc0-311c-436e-8d01-04159d1a4f1c)
![notifications](https://github.com/goksan/statusnook/assets/17437810/80564b2c-fb2d-47e5-9b74-781b7e9a264c)



