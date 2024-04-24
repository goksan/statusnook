variable "token" {
  type = string
}


packer {
    required_plugins {
        digitalocean = {
            version = ">= 1.3.0"
            source  = "github.com/digitalocean/digitalocean"
        }
    }
}

source "digitalocean" "statusnook" {
    api_token    = var.token
    image        = "ubuntu-22-04-x64"
    region       = "fra1"
    size         = "s-1vcpu-512mb-10gb"
    ssh_username = "root"
}

build {
  sources = ["source.digitalocean.statusnook"]

  provisioner "shell" {
    scripts = [
        "scripts/01-statusnook.sh",
        "scripts/02-ufw.sh",
        "scripts/90-cleanup.sh",
        "scripts/99-img-check.sh"
    ]
  }
}