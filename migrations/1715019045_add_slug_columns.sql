alter table
    service rename to old__service;

alter table
    alert_service rename to old__alert_service;

alter table
    monitor rename to old__monitor;

alter table
    monitor_log rename to old__monitor_log;

drop index idx_monitor_log_monitor_id_started_at;

alter table
    monitor_log_last_checked rename to old__monitor_log_last_checked;

alter table
    notification_channel rename to old__notification_channel;

alter table
    monitor_notification_channel rename to old__monitor_notification_channel;

alter table
    alert_setting_smtp_notification rename to old__alert_setting_smtp_notification;

alter table
    mail_group rename to old__mail_group;

alter table
    mail_group_member rename to old__mail_group_member;

alter table
    mail_group_monitor rename to old__mail_group_monitor;

create table service(
    id integer primary key,
    slug text not null unique,
    name text not null,
    helper_text text not null
);

create table alert_service(
    id integer primary key,
    alert_id int references alert(id) on delete cascade not null,
    service_id int references service(id) on delete cascade not null
);

create table monitor(
    id integer primary key,
    slug text not null unique,
    name text not null,
    url text not null,
    method text not null,
    frequency integer not null,
    timeout integer not null,
    attempts integer not null,
    request_headers text,
    body_format text,
    body text
);

create table monitor_log(
    id integer primary key,
    started_at datetime not null,
    ended_at datetime not null,
    response_code integer,
    error_message text,
    attempts integer not null,
    result text not null,
    monitor_id int references monitor(id) on delete cascade not null
);

create index idx_monitor_log_monitor_id_started_at on monitor_log(monitor_id, started_at);

create table monitor_log_last_checked(
    id integer primary key,
    checked_at datetime not null,
    monitor_id int int references monitor(id) on delete cascade not null unique,
    monitor_log_id int references monitor_log(id) on delete cascade not null unique
);

create table notification_channel(
    id integer primary key,
    slug text not null unique,
    name text not null,
    type text not null check(type in ('smtp', 'slack')),
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

create table mail_group(
    id integer primary key,
    slug text not null unique,
    name text not null,
    description text
);

create table mail_group_member(
    id integer primary key,
    email_address text not null collate nocase,
    mail_group_id int references mail_group(id) on delete cascade not null,
    unique(mail_group_id, email_address)
);

create table mail_group_monitor(
    id integer primary key,
    mail_group_id int references mail_group(id) on delete cascade not null,
    monitor_id int references monitor(id) on delete cascade not null,
    unique(mail_group_id, monitor_id)
);