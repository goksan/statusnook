
<p align="center">
  <a href="https://statusnook.com" target="_blank">
    <img width="245px" src="https://github.com/goksan/statusnook/assets/17437810/0b8bea4c-16cc-4d57-a984-49f01aca85d7">
  </a>
</p>

<p align="center">
Effortlessly deploy a status page and start monitoring endpoints in minutes
</p>

![status page](https://github.com/goksan/statusnook/assets/17437810/ff2bb1d4-5d75-4b6e-b8d9-a7227d1aee6c)

<br>


## Deployment paths

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
Pending approval by DigitalOcean

## Gallery

![monitors](https://github.com/goksan/statusnook/assets/17437810/9bc9a023-41fc-4646-a353-0a1755ce148b)
![monitor logs](https://github.com/goksan/statusnook/assets/17437810/23d988b1-a9fe-41a4-9fa3-f524c4612958)
![notifications](https://github.com/goksan/statusnook/assets/17437810/ff35893c-d4eb-4bb5-af1b-9f07e716265a)



