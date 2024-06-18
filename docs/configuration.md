# Configuration

By default, you can configure your Statusnook instance through the standard web UI.

Through the settings page, you can opt for an exclusively text-based configuration. This disables elements of the standard interface and allows you to manage the configuration via text.

Additionally, you can set opt for updates to be managed solely through GitHub, enabling automatic synchronisation with your Statusnook instance on pushes to a chosen branch.


> [!CAUTION]
> Dropping or renaming keys is a destructive action (mail groups, notification channels, monitors, services)
>
>[See "Renaming A Resource Key"](#renaming-a-resource-key)

## Example config.yaml

```yaml
general-settings:
  name: Statusnook
mail-groups:
  core:
    name: Core
    members:
      - core1@example.com
      - core2@example.com
  engineers:
    name: Engineers
    description: All engineers in our organisation
    members:
      - engineer1@example.com
notification-channels:
  azure:
    from: example@example.com
    host: smtp.azurecomm.net
    name: Azure
    password: secret_Qg6RqkWLe1m4a6TzK+grCcgRIQsiFEc95nJXMsLBZIZSyA==.tOw0xDcUdmmr62tJ
    port: 587
    type: smtp
    username: example
  postmark:
    from: example@example.com
    host: smtp.postmarkapp.com
    misc:
      pm-broadcast: broadcast
      pm-transactional: outbound
    name: Postmark
    password: secret_hyNDZ3rL5ee7eco6DCoGnKcVsksZFY4MMb3b4JsCwbGh3A==.YwiY1DgH0ExUsDmJ
    port: 587
    type: smtp
    username: secret_hyNDZ3rL5ee7eco6DCoGnKcVsksZFY4MMb3b4JsCwbGh3A==.YwiY1DgH0ExUsDmJ
  ses:
    from: example@example.com
    host: email-smtp.eu-north-1.amazonaws.com
    name: SES
    password: secret_ZYjE7eePnHBlQph6pK0e30yeVpovb37h/VvcJbPw96fbHg==./1e5EXv1iUF8Y6XY
    port: 587
    type: smtp
    username: example
  slack-internal-alerts:
    name: "Slack #internal-alerts"
    type: slack
    webhook-url: secret_4//EgNno+/nZwEiO44TQ4k/9FNLbh2zNJc8hJqWIwTIc0Q==.eoLscWK0jMFRkgWa
monitors:
  get:
    name: Example
    url: https://example.com
    method: GET
    frequency: 10
    timeout: 5
    attempts: 1
    notification-channels:
      - azure
      - postmark
  post-form:
    name: Post form example
    url: https://example.com
    method: POST
    frequency: 10
    timeout: 5
    attempts: 1
    headers:
      Content-Type: application/x-www-form-urlencoded
    body:
      example-name: example-value
    notification-channels:
      - ses
    mail-groups:
      - engineers
      - core
  post-json:
    name: Post json example
    url: https://example.com
    method: POST
    frequency: 10
    timeout: 5
    attempts: 1
    headers:
      Content-Type: application/json
    body: '{"key1": "value1", "key2": "value2"}'
    notification-channels:
      - azure
    mail-groups:
      - core
services:
  website:
    name: Website
    description: example.com
  api:
    name: API
    description: api.example.com
alert-notification-settings:
  email-notification-channel: postmark
  managed-subscriptions: true
  slack-client-secret: secret_tdBs7fxa31U+Nc31MUWBVea5pdT6ycHUsCOXfw==.M/qsy+BDnJoMALin
  slack-install-url: https://slack.com/oauth/v2/authorize?...
```

## Renaming a Resource Key
Below is an example demonstrating how to change the `engineers` mail group key to `engineering-team`

```yaml
rename:
  mail-groups.engineers: engineering-team
mail-groups:
  engineering-team:
    name: Engineers
    description: All engineers in our organisation
    members:
      - engineer1@example.com
# The rest of the config is omitted for demonstration purposes. Retain the rest of your config!
```

In addition to adding the rename section, update all references to `engineers` with `engineering-team` and apply this configuration to execute the rename.

After completing the rename, remove the `rename` section or at least the outdated part from your configuration, and reapply the configuration to ensure that future changes are applied successfully.

## Secrets
Secrets can be encrypted and decrypted via the settings page.

<img src="https://github.com/goksan/statusnook/assets/17437810/78753b51-534a-4116-b5a7-6ba4dd05c7f7" width="800">
<br><br>

When Statusnook is applying a configuration it attempts to decrypt and replace any value prefixed with `secret_`.

