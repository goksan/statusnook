#!/bin/bash

ufw limit ssh   
sudo ufw allow https
sudo ufw allow http
ufw --force enable
