alter table
    notification_channel rename to old__notification_channel;

alter table
    monitor_notification_channel rename to old__monitor_notification_channel;

alter table
    alert_setting_smtp_notification rename to old__alert_setting_smtp_notification;

create table notification_channel(
    id integer primary key,
    slug text not null unique,
    name text not null,
    type text not null,
    details text not null
);

create table monitor_notification_channel(
    id integer primary key,
    monitor_id int references monitor(id) on delete cascade not null,
    notification_channel_id int references notification_channel(id) on delete cascade not null,
    unique(monitor_id, notification_channel_id)
);

create table alert_setting_smtp_notification(
    id integer primary key,
    notification_channel_id int references notification_channel(id) on delete cascade not null unique
);

insert into
    notification_channel(id, slug, name, type, details)
select
    id,
    slug,
    name,
    type,
    details
from
    old__notification_channel;

insert into
    monitor_notification_channel(id, monitor_id, notification_channel_id)
select
    id,
    monitor_id,
    notification_channel_id
from
    old__monitor_notification_channel;

insert into
    alert_setting_smtp_notification(id, notification_channel_id)
select
    id,
    notification_channel_id
from
    old__alert_setting_smtp_notification;

drop table old__alert_setting_smtp_notification;

drop table old__monitor_notification_channel;

drop table old__notification_channel;